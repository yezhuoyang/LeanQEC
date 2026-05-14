import QStab.Paper.BB72ChainAttackFullZ

/-!
# Final Z-side discharge: bb_NZ_no_Z_attack_below_6 is a theorem

Composes the Z-side chain attack discharge (`bb_chain_attack_Z_le_5`)
with the reachableE → chain XOR bridge (`reachableE_zContent_chain`)
and the bb_isSuccessZside bridge.
-/

namespace QStab.Paper.BB72ReachableEBridgeZ

open QStab QStab.Paper.BB72Instance QStab.Paper.BB72JointInstance QStab.Paper.BB72BVZ
open QStab.Paper.GenericReachableBridge

/-! ## Bridge: bb_isSuccessZside (zContent E) = false → bb_isSuccessZside E = false -/

/-- For any stab index `i : Fin 72` with `i.val < 36`, `i = xStabIdx ⟨i.val, _⟩`. -/
theorem stab_idx_lt_36_eq_xStabIdx (i : Fin 72) (hi : i.val < 36) :
    i = xStabIdx ⟨i.val, hi⟩ := by
  unfold xStabIdx
  ext
  rfl

/-- If `bb_isSuccessZside (zContent E) = false`, then `bb_isSuccessZside E = false`. -/
theorem bb_isSuccessZside_of_zContent_false (E : ErrorVec 72)
    (h : bb_isSuccessZside (zContent E) = false) : bb_isSuccessZside E = false := by
  unfold bb_isSuccessZside at h ⊢
  rw [Bool.and_eq_false_iff] at h ⊢
  rcases h with hstab | hlx
  · -- Some stab parity is true for zContent E
    left
    rw [List.all_eq_false] at hstab ⊢
    obtain ⟨i, hi_mem, hpari⟩ := hstab
    have hpari_true : ErrorVec.parity (bb_stabilizers i) (zContent E) = true := by
      rw [Bool.not_eq_true, decide_eq_false_iff_not] at hpari
      cases h_par : ErrorVec.parity (bb_stabilizers i) (zContent E)
      · exact absurd h_par hpari
      · rfl
    by_cases hX : i.val < 36
    · -- X-stab case (i.val < 36): use parity_xstab_eq_zContent
      refine ⟨i, hi_mem, ?_⟩
      rw [Bool.not_eq_true, decide_eq_false_iff_not]
      intro hpari_E_false
      rw [parity_xstab_eq_zContent i hX] at hpari_E_false
      rw [hpari_E_false] at hpari_true
      exact Bool.false_ne_true hpari_true
    · -- Z-stab case (i.val ≥ 36): contradicts since Z-only × Z-only = 0
      exfalso
      push_neg at hX
      let s : Fin 36 := ⟨i.val - 36, by omega⟩
      have heq : i = QStab.Paper.BB72BVBridge.zStabIdx s := by
        unfold QStab.Paper.BB72BVBridge.zStabIdx
        ext
        show i.val = (i.val - 36) + 36
        omega
      have h_zonly_stab : is_Z_only_ev (bb_stabilizers i) = true := by
        rw [heq, is_Z_only_ev_iff]
        have := QStab.Paper.BB72BVBridge.is_Z_only_bb_zstab s
        rw [QStab.Paper.BB72BVBridge.is_Z_only_iff] at this
        exact this
      have h_zonly_zc : is_Z_only_ev (zContent E) = true := zContent_is_Z_only E
      rw [parity_Z_only_Z_only _ _ h_zonly_stab h_zonly_zc] at hpari_true
      exact Bool.false_ne_true hpari_true
  · -- All L_X parities are false for zContent E
    right
    rw [List.any_eq_false] at hlx ⊢
    intro l hl_mem
    have : ErrorVec.parity (bb_logicalX_basis l) (zContent E) ≠ true :=
      hlx l hl_mem
    rw [← parity_lx_eq_zContent] at this
    exact this

/-! ## Final theorem: discharge bb_NZ_no_Z_attack_below_6 -/

open QStab.Paper.BB72ChainAttackFullZ in
/-- **Main result**: for any `E ∈ reachableE bb_allHooksZ 5`, `bb_isSuccessZside E = false`.
    This discharges the `bb_NZ_no_Z_attack_below_6` axiom. -/
theorem bb_NZ_no_Z_attack_below_6_proven :
    ∀ E ∈ reachableE bb_allHooksZ bb_jointCode.C_budget, bb_isSuccessZside E = false := by
  intro E hE
  have hbudget : bb_jointCode.C_budget = 5 := by rfl
  rw [hbudget] at hE
  obtain ⟨chain, hlen, hxor⟩ := reachableE_zContent_chain 5 E hE
  have h_chain_false : bb_chain_attack_Z chain = false :=
    bb_chain_attack_Z_le_5 chain hlen
  have h_zc_false : bb_isSuccessZside (zContent E) = false := by
    unfold bb_chain_attack_Z at h_chain_false
    rw [hxor] at h_chain_false
    exact h_chain_false
  exact bb_isSuccessZside_of_zContent_false E h_zc_false

end QStab.Paper.BB72ReachableEBridgeZ

/-! ## Re-export into `QStab.Paper.BB72JointInstance` namespace

The original axiom `bb_NZ_no_Z_attack_below_6` was declared in
`QStab.Paper.BB72JointInstance`. We redeclare it here as a theorem
using the proven version. -/

namespace QStab.Paper.BB72JointInstance

open QStab QStab.Paper.GenericReachableBridge QStab.Paper.BB72Instance
  QStab.Paper.SurfaceD3JointXZ

/-- **PROVEN** (formerly axiom): BB72 NZ Z-side per-scheduling finite check. -/
theorem bb_NZ_no_Z_attack_below_6 :
    ∀ E ∈ reachableE bb_allHooksZ bb_jointCode.C_budget, bb_isSuccessZside E = false :=
  QStab.Paper.BB72ReachableEBridgeZ.bb_NZ_no_Z_attack_below_6_proven

/-- **BB [[72, 12, 6]] joint d_circ ≥ 6**: now unconditional. -/
theorem bb_NZ_joint_d_circ_ge_6 :
    ∀ (s : State bb_jointCode),
      MultiStep bb_jointCode (.active (State.init bb_jointCode)) (.active s) →
      bb_isSuccessJoint s.E_tilde = false := by
  intro s hreach
  have h_x_in : xPartE s.E_tilde ∈ reachableE bb_allHooks (bb_jointCode.C_budget - s.C) :=
    bb_joint_xPart_in_X_reachable s hreach
  have h_z_in : zPartE s.E_tilde ∈ reachableE bb_allHooksZ (bb_jointCode.C_budget - s.C) :=
    bb_joint_zPart_in_Z_reachable s hreach
  have h_le : bb_jointCode.C_budget - s.C ≤ bb_jointCode.C_budget := Nat.sub_le _ _
  have h_x_in_full : xPartE s.E_tilde ∈ reachableE bb_allHooks bb_jointCode.C_budget :=
    reachableE_mono_le bb_allHooks h_le _ h_x_in
  have h_z_in_full : zPartE s.E_tilde ∈ reachableE bb_allHooksZ bb_jointCode.C_budget :=
    reachableE_mono_le bb_allHooksZ h_le _ h_z_in
  have h_budget_eq : bb_code.C_budget = bb_jointCode.C_budget := rfl
  rw [← h_budget_eq] at h_x_in_full
  have h_x_no : bb_isSuccess (xPartE s.E_tilde) = false :=
    QStab.Paper.BB72Instance.bb_NZ_no_X_attack_below_6 (xPartE s.E_tilde) h_x_in_full
  have h_z_no : bb_isSuccessZside (zPartE s.E_tilde) = false :=
    bb_NZ_no_Z_attack_below_6 (zPartE s.E_tilde) h_z_in_full
  unfold bb_isSuccessJoint
  by_contra h_succ
  have h_succ_true : (((List.finRange 72).all fun i =>
        ErrorVec.parity (bb_stabilizers i) s.E_tilde = false) &&
      (((List.finRange 12).any fun i => ErrorVec.parity (bb_logicalZ_basis i) s.E_tilde) ||
       ((List.finRange 12).any fun i => ErrorVec.parity (bb_logicalX_basis i) s.E_tilde))) = true := by
    cases hh : (((List.finRange 72).all fun i =>
        ErrorVec.parity (bb_stabilizers i) s.E_tilde = false) &&
        (((List.finRange 12).any fun i => ErrorVec.parity (bb_logicalZ_basis i) s.E_tilde) ||
         ((List.finRange 12).any fun i => ErrorVec.parity (bb_logicalX_basis i) s.E_tilde)))
    · exact absurd hh h_succ
    · rfl
  rw [Bool.and_eq_true] at h_succ_true
  obtain ⟨h_zero_syn, h_some_l⟩ := h_succ_true
  rw [List.all_eq_true] at h_zero_syn
  rw [Bool.or_eq_true] at h_some_l
  rcases h_some_l with h_lZ | h_lX
  · have h_zSyn_x : ∀ i : Fin 72,
        ErrorVec.parity (bb_stabilizers i) (xPartE s.E_tilde) = false := by
      intro i
      by_cases hi_x : i.val < 36
      · have h_xonly := bb_stabilizers_xOnly_at_xStabIdx i hi_x
        have h_xPart_xonly : ∀ j, (xPartE s.E_tilde) j = .X ∨ (xPartE s.E_tilde) j = .I := by
          intro j; unfold xPartE Pauli.xPartL; cases s.E_tilde j <;> simp
        exact parity_xStab_xOnly_zero _ _ h_xonly h_xPart_xonly
      · have hi_z : i.val ≥ 36 := Nat.le_of_not_lt hi_x
        have h_zonly := bb_stabilizers_zOnly_at_zStabIdx i hi_z
        have h_eq : ErrorVec.parity (bb_stabilizers i) s.E_tilde =
                    ErrorVec.parity (bb_stabilizers i) (xPartE s.E_tilde) :=
          parity_zStab_eq_xPart _ _ h_zonly
        rw [← h_eq]
        have := h_zero_syn i (List.mem_finRange i)
        simpa using this
    have h_lZ_basis_zOnly : ∀ k : Fin 12, isZOnly (bb_logicalZ_basis k) := by
      intro k
      have h_dec : ∀ j : Fin 12, ∀ q : Fin 72,
          (bb_logicalZ_basis j) q = .Z ∨ (bb_logicalZ_basis j) q = .I := by
        native_decide
      intro q; exact h_dec k q
    rw [List.any_eq_true] at h_lZ
    rcases h_lZ with ⟨k, _, h_lZk⟩
    have h_lZk_decomp : ErrorVec.parity (bb_logicalZ_basis k) s.E_tilde =
                       ErrorVec.parity (bb_logicalZ_basis k) (xPartE s.E_tilde) :=
      parity_zStab_eq_xPart _ _ (h_lZ_basis_zOnly k)
    rw [h_lZk_decomp] at h_lZk
    have h_xSucc : bb_isSuccess (xPartE s.E_tilde) = true := by
      unfold bb_isSuccess
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [List.all_eq_true]; intro i _; simpa using h_zSyn_x i
      · rw [List.any_eq_true]; exact ⟨k, List.mem_finRange k, h_lZk⟩
    rw [h_xSucc] at h_x_no
    exact absurd h_x_no (by decide)
  · have h_xSyn_z : ∀ i : Fin 72,
        ErrorVec.parity (bb_stabilizers i) (zPartE s.E_tilde) = false := by
      intro i
      by_cases hi_x : i.val < 36
      · have h_xonly := bb_stabilizers_xOnly_at_xStabIdx i hi_x
        have h_eq : ErrorVec.parity (bb_stabilizers i) s.E_tilde =
                    ErrorVec.parity (bb_stabilizers i) (zPartE s.E_tilde) :=
          parity_xStab_eq_zPart _ _ h_xonly
        rw [← h_eq]
        have := h_zero_syn i (List.mem_finRange i)
        simpa using this
      · have hi_z : i.val ≥ 36 := Nat.le_of_not_lt hi_x
        have h_zonly := bb_stabilizers_zOnly_at_zStabIdx i hi_z
        have h_zPart_zonly : ∀ j, (zPartE s.E_tilde) j = .Z ∨ (zPartE s.E_tilde) j = .I := by
          intro j; unfold zPartE Pauli.zPartL; cases s.E_tilde j <;> simp
        exact parity_zStab_zOnly_zero _ _ h_zonly h_zPart_zonly
    have h_lX_basis_xOnly : ∀ k : Fin 12, isXOnly (bb_logicalX_basis k) := by
      intro k
      have h_dec : ∀ j : Fin 12, ∀ q : Fin 72,
          (bb_logicalX_basis j) q = .X ∨ (bb_logicalX_basis j) q = .I := by
        native_decide
      intro q; exact h_dec k q
    rw [List.any_eq_true] at h_lX
    rcases h_lX with ⟨k, _, h_lXk⟩
    have h_lXk_decomp : ErrorVec.parity (bb_logicalX_basis k) s.E_tilde =
                       ErrorVec.parity (bb_logicalX_basis k) (zPartE s.E_tilde) :=
      parity_xStab_eq_zPart _ _ (h_lX_basis_xOnly k)
    rw [h_lXk_decomp] at h_lXk
    have h_zSucc : bb_isSuccessZside (zPartE s.E_tilde) = true := by
      unfold bb_isSuccessZside
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [List.all_eq_true]; intro i _; simpa using h_xSyn_z i
      · rw [List.any_eq_true]; exact ⟨k, List.mem_finRange k, h_lXk⟩
    rw [h_zSucc] at h_z_no
    exact absurd h_z_no (by decide)

/-- **Invariant-form joint non-success** (lifts the body of
    `bb_NZ_joint_d_circ_ge_6` to take the joint bridge invariant
    directly, rather than going via `MultiStep`). This is exactly the
    shape required by a `QStabFTCertificate`'s `bridge` field: from the
    dynamic invariant on a state, conclude the failure predicate
    cannot hold. -/
theorem bb_NZ_no_joint_success_of_invariant (s : State bb_jointCode)
    (hinv : QStab.Paper.BB72JointInstance.bb_jointBridgePred s) :
    bb_isSuccessJoint s.E_tilde = false := by
  obtain ⟨h_x_in, h_z_in, _h_C⟩ := hinv
  have h_le : bb_jointCode.C_budget - s.C ≤ bb_jointCode.C_budget := Nat.sub_le _ _
  have h_x_in_full : xPartE s.E_tilde ∈ reachableE bb_allHooks bb_jointCode.C_budget :=
    reachableE_mono_le bb_allHooks h_le _ h_x_in
  have h_z_in_full : zPartE s.E_tilde ∈ reachableE bb_allHooksZ bb_jointCode.C_budget :=
    reachableE_mono_le bb_allHooksZ h_le _ h_z_in
  have h_budget_eq : bb_code.C_budget = bb_jointCode.C_budget := rfl
  rw [← h_budget_eq] at h_x_in_full
  have h_x_no : bb_isSuccess (xPartE s.E_tilde) = false :=
    QStab.Paper.BB72Instance.bb_NZ_no_X_attack_below_6 (xPartE s.E_tilde) h_x_in_full
  have h_z_no : bb_isSuccessZside (zPartE s.E_tilde) = false :=
    bb_NZ_no_Z_attack_below_6 (zPartE s.E_tilde) h_z_in_full
  unfold bb_isSuccessJoint
  by_contra h_succ
  have h_succ_true : (((List.finRange 72).all fun i =>
        ErrorVec.parity (bb_stabilizers i) s.E_tilde = false) &&
      (((List.finRange 12).any fun i => ErrorVec.parity (bb_logicalZ_basis i) s.E_tilde) ||
       ((List.finRange 12).any fun i => ErrorVec.parity (bb_logicalX_basis i) s.E_tilde))) = true := by
    cases hh : (((List.finRange 72).all fun i =>
        ErrorVec.parity (bb_stabilizers i) s.E_tilde = false) &&
        (((List.finRange 12).any fun i => ErrorVec.parity (bb_logicalZ_basis i) s.E_tilde) ||
         ((List.finRange 12).any fun i => ErrorVec.parity (bb_logicalX_basis i) s.E_tilde)))
    · exact absurd hh h_succ
    · rfl
  rw [Bool.and_eq_true] at h_succ_true
  obtain ⟨h_zero_syn, h_some_l⟩ := h_succ_true
  rw [List.all_eq_true] at h_zero_syn
  rw [Bool.or_eq_true] at h_some_l
  rcases h_some_l with h_lZ | h_lX
  · have h_zSyn_x : ∀ i : Fin 72,
        ErrorVec.parity (bb_stabilizers i) (xPartE s.E_tilde) = false := by
      intro i
      by_cases hi_x : i.val < 36
      · have h_xonly := bb_stabilizers_xOnly_at_xStabIdx i hi_x
        have h_xPart_xonly : ∀ j, (xPartE s.E_tilde) j = .X ∨ (xPartE s.E_tilde) j = .I := by
          intro j; unfold xPartE Pauli.xPartL; cases s.E_tilde j <;> simp
        exact parity_xStab_xOnly_zero _ _ h_xonly h_xPart_xonly
      · have hi_z : i.val ≥ 36 := Nat.le_of_not_lt hi_x
        have h_zonly := bb_stabilizers_zOnly_at_zStabIdx i hi_z
        have h_eq : ErrorVec.parity (bb_stabilizers i) s.E_tilde =
                    ErrorVec.parity (bb_stabilizers i) (xPartE s.E_tilde) :=
          parity_zStab_eq_xPart _ _ h_zonly
        rw [← h_eq]
        have := h_zero_syn i (List.mem_finRange i)
        simpa using this
    have h_lZ_basis_zOnly : ∀ k : Fin 12, isZOnly (bb_logicalZ_basis k) := by
      intro k
      have h_dec : ∀ j : Fin 12, ∀ q : Fin 72,
          (bb_logicalZ_basis j) q = .Z ∨ (bb_logicalZ_basis j) q = .I := by
        native_decide
      intro q; exact h_dec k q
    rw [List.any_eq_true] at h_lZ
    rcases h_lZ with ⟨k, _, h_lZk⟩
    have h_lZk_decomp : ErrorVec.parity (bb_logicalZ_basis k) s.E_tilde =
                       ErrorVec.parity (bb_logicalZ_basis k) (xPartE s.E_tilde) :=
      parity_zStab_eq_xPart _ _ (h_lZ_basis_zOnly k)
    rw [h_lZk_decomp] at h_lZk
    have h_xSucc : bb_isSuccess (xPartE s.E_tilde) = true := by
      unfold bb_isSuccess
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [List.all_eq_true]; intro i _; simpa using h_zSyn_x i
      · rw [List.any_eq_true]; exact ⟨k, List.mem_finRange k, h_lZk⟩
    rw [h_xSucc] at h_x_no
    exact absurd h_x_no (by decide)
  · have h_xSyn_z : ∀ i : Fin 72,
        ErrorVec.parity (bb_stabilizers i) (zPartE s.E_tilde) = false := by
      intro i
      by_cases hi_x : i.val < 36
      · have h_xonly := bb_stabilizers_xOnly_at_xStabIdx i hi_x
        have h_eq : ErrorVec.parity (bb_stabilizers i) s.E_tilde =
                    ErrorVec.parity (bb_stabilizers i) (zPartE s.E_tilde) :=
          parity_xStab_eq_zPart _ _ h_xonly
        rw [← h_eq]
        have := h_zero_syn i (List.mem_finRange i)
        simpa using this
      · have hi_z : i.val ≥ 36 := Nat.le_of_not_lt hi_x
        have h_zonly := bb_stabilizers_zOnly_at_zStabIdx i hi_z
        have h_zPart_zonly : ∀ j, (zPartE s.E_tilde) j = .Z ∨ (zPartE s.E_tilde) j = .I := by
          intro j; unfold zPartE Pauli.zPartL; cases s.E_tilde j <;> simp
        exact parity_zStab_zOnly_zero _ _ h_zonly h_zPart_zonly
    have h_lX_basis_xOnly : ∀ k : Fin 12, isXOnly (bb_logicalX_basis k) := by
      intro k
      have h_dec : ∀ j : Fin 12, ∀ q : Fin 72,
          (bb_logicalX_basis j) q = .X ∨ (bb_logicalX_basis j) q = .I := by
        native_decide
      intro q; exact h_dec k q
    rw [List.any_eq_true] at h_lX
    rcases h_lX with ⟨k, _, h_lXk⟩
    have h_lXk_decomp : ErrorVec.parity (bb_logicalX_basis k) s.E_tilde =
                       ErrorVec.parity (bb_logicalX_basis k) (zPartE s.E_tilde) :=
      parity_xStab_eq_zPart _ _ (h_lX_basis_xOnly k)
    rw [h_lXk_decomp] at h_lXk
    have h_zSucc : bb_isSuccessZside (zPartE s.E_tilde) = true := by
      unfold bb_isSuccessZside
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [List.all_eq_true]; intro i _; simpa using h_xSyn_z i
      · rw [List.any_eq_true]; exact ⟨k, List.mem_finRange k, h_lXk⟩
    rw [h_zSucc] at h_z_no
    exact absurd h_z_no (by decide)

end QStab.Paper.BB72JointInstance
