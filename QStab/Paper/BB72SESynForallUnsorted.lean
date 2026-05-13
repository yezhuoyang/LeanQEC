import QStab.Paper.BB72SESynVerify

namespace QStab.Paper.BB72BVSE

/-- **No 4-tuple of SE mechs is an attack** (unsorted, allows duplicates). ~97 min build. -/
theorem no_4_chain_attack_unsorted_SE :
    ∀ (i j k l : Fin 252),
      ¬ (mech_se_syn i ^^^ mech_se_syn j ^^^ mech_se_syn k ^^^ mech_se_syn l = 0 ∧
         mech_se_lz i ^^^ mech_se_lz j ^^^ mech_se_lz k ^^^ mech_se_lz l ≠ 0) := by
  native_decide

end QStab.Paper.BB72BVSE
