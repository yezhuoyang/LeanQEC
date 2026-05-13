import QStab.Paper.BB72SESynForallUnsorted
import QStab.Paper.BB72SEChainAttack

namespace QStab.Paper.BB72SEChainAttackK4

open QStab.Paper.BB72BVSE

theorem bb_chain_attack_SE_k4 :
    ∀ chain : List (Fin 252), chain.length = 4 →
      bb_chain_attack_SE chain = false := by
  intro chain h
  match chain, h with
  | [a, b, c, d], _ =>
    by_contra hatt
    rw [Bool.not_eq_false] at hatt
    obtain ⟨hsyn, hlz⟩ := (bb_chain_attack_SE_iff_syn _).mp hatt
    apply no_4_chain_attack_unsorted_SE a b c d
    refine ⟨?_, ?_⟩
    · have h1 : chain_xor_se_syn [a, b, c, d] =
          mech_se_syn a ^^^ mech_se_syn b ^^^ mech_se_syn c ^^^ mech_se_syn d := by
        show mech_se_syn a ^^^ (mech_se_syn b ^^^ (mech_se_syn c ^^^ (mech_se_syn d ^^^ 0))) = _
        simp [BitVec.xor_assoc]
      rw [← h1]; exact hsyn
    · have h2 : chain_xor_se_lz [a, b, c, d] =
          mech_se_lz a ^^^ mech_se_lz b ^^^ mech_se_lz c ^^^ mech_se_lz d := by
        show mech_se_lz a ^^^ (mech_se_lz b ^^^ (mech_se_lz c ^^^ (mech_se_lz d ^^^ 0))) = _
        simp [BitVec.xor_assoc]
      rw [← h2]; exact hlz

end QStab.Paper.BB72SEChainAttackK4
