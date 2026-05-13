import QStab.Paper.BB72SESynVerify

namespace QStab.Paper.BB72BVSE

theorem no_1_chain_attack_SE :
    ∀ (a : Fin 252),
      ¬ (mech_se_syn a = 0 ∧ mech_se_lz a ≠ 0) := by
  native_decide

theorem no_3_chain_attack_sorted_SE :
    ∀ (i j k : Fin 252), i.val < j.val → j.val < k.val →
      ¬ (mech_se_syn i ^^^ mech_se_syn j ^^^ mech_se_syn k = 0 ∧
         mech_se_lz i ^^^ mech_se_lz j ^^^ mech_se_lz k ≠ 0) := by
  native_decide

theorem no_4_chain_attack_sorted_SE :
    ∀ (i j k l : Fin 252), i.val < j.val → j.val < k.val → k.val < l.val →
      ¬ (mech_se_syn i ^^^ mech_se_syn j ^^^ mech_se_syn k ^^^ mech_se_syn l = 0 ∧
         mech_se_lz i ^^^ mech_se_lz j ^^^ mech_se_lz k ^^^ mech_se_lz l ≠ 0) := by
  native_decide

end QStab.Paper.BB72BVSE
