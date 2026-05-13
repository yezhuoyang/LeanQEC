import QStab.Paper.BB72SESynBridge
import QStab.Paper.BB72SEChainCheck

namespace QStab.Paper.BB72BVSE

open QStab QStab.Paper.BB72SEInstance QStab.Paper.BB72ReachableEBridgeSE
  QStab.Paper.BB72SEChainCheck

@[simp] theorem chain_xor_SE_singleton (i : Fin 252) :
    chain_xor_SE [i] = bb_se_xMech i := by
  unfold chain_xor_SE
  show ErrorVec.mul (bb_se_xMech i) (ErrorVec.identity 72) = bb_se_xMech i
  unfold ErrorVec.mul ErrorVec.identity
  funext q
  generalize bb_se_xMech i q = p
  cases p <;> rfl

theorem bb_chain_attack_SE_k0 :
    ∀ chain : List (Fin 252), chain.length = 0 →
      bb_chain_attack_SE chain = false := by
  intro chain h
  rw [List.length_eq_zero_iff] at h
  rw [h]
  unfold bb_chain_attack_SE chain_xor_SE bb_se_isSuccess
  simp [ErrorVec.parity_identity]

theorem bb_chain_attack_SE_k1 :
    ∀ chain : List (Fin 252), chain.length = 1 →
      bb_chain_attack_SE chain = false := by
  intro chain h
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp h
  unfold bb_chain_attack_SE
  rw [chain_xor_SE_singleton]
  exact bb_se_chain_1_no_attack i

@[simp] theorem chain_xor_SE_pair (i j : Fin 252) :
    chain_xor_SE [i, j] = ErrorVec.mul (bb_se_xMech i) (bb_se_xMech j) := by
  show ErrorVec.mul (bb_se_xMech i) (chain_xor_SE [j]) = _
  rw [chain_xor_SE_singleton]

theorem bb_chain_attack_SE_k2 :
    ∀ chain : List (Fin 252), chain.length = 2 →
      bb_chain_attack_SE chain = false := by
  intro chain h
  match chain, h with
  | [i, j], _ =>
    unfold bb_chain_attack_SE
    rw [chain_xor_SE_pair]
    exact bb_se_chain_2_no_attack i j

/-- **No length-3 SE chain is a successful X-side attack** (direct native_decide on syndrome form). -/
theorem bb_chain_attack_SE_k3_syn :
    ∀ (i j k : Fin 252),
      ¬ (mech_se_syn i ^^^ mech_se_syn j ^^^ mech_se_syn k = 0 ∧
         mech_se_lz i ^^^ mech_se_lz j ^^^ mech_se_lz k ≠ 0) := by
  native_decide

theorem bb_chain_attack_SE_k3 :
    ∀ chain : List (Fin 252), chain.length = 3 →
      bb_chain_attack_SE chain = false := by
  intro chain h
  match chain, h with
  | [i, j, k], _ =>
    by_contra hatt
    rw [Bool.not_eq_false] at hatt
    obtain ⟨hsyn, hlz⟩ := (bb_chain_attack_SE_iff_syn _).mp hatt
    apply bb_chain_attack_SE_k3_syn i j k
    refine ⟨?_, ?_⟩
    · have h1 : chain_xor_se_syn [i, j, k] =
          mech_se_syn i ^^^ mech_se_syn j ^^^ mech_se_syn k := by
        show mech_se_syn i ^^^ (mech_se_syn j ^^^ (mech_se_syn k ^^^ 0)) = _
        simp [BitVec.xor_assoc]
      rw [← h1]; exact hsyn
    · have h2 : chain_xor_se_lz [i, j, k] =
          mech_se_lz i ^^^ mech_se_lz j ^^^ mech_se_lz k := by
        show mech_se_lz i ^^^ (mech_se_lz j ^^^ (mech_se_lz k ^^^ 0)) = _
        simp [BitVec.xor_assoc]
      rw [← h2]; exact hlz

end QStab.Paper.BB72BVSE
