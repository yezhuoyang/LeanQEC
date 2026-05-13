import QStab.Paper.BB72SESynBridge

open List

namespace QStab.Paper.BB72BVSE

theorem chain_xor_se_syn_perm {c c' : List (Fin 252)} (h : c ~ c') :
    chain_xor_se_syn c = chain_xor_se_syn c' := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [chain_xor_se_syn, ih]
  | swap a b rest =>
    show mech_se_syn b ^^^ (mech_se_syn a ^^^ chain_xor_se_syn rest) =
         mech_se_syn a ^^^ (mech_se_syn b ^^^ chain_xor_se_syn rest)
    calc mech_se_syn b ^^^ (mech_se_syn a ^^^ chain_xor_se_syn rest)
        = (mech_se_syn b ^^^ mech_se_syn a) ^^^ chain_xor_se_syn rest := by
          rw [← BitVec.xor_assoc]
      _ = (mech_se_syn a ^^^ mech_se_syn b) ^^^ chain_xor_se_syn rest := by
          rw [BitVec.xor_comm (mech_se_syn b) (mech_se_syn a)]
      _ = mech_se_syn a ^^^ (mech_se_syn b ^^^ chain_xor_se_syn rest) := BitVec.xor_assoc _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem chain_xor_se_lz_perm {c c' : List (Fin 252)} (h : c ~ c') :
    chain_xor_se_lz c = chain_xor_se_lz c' := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [chain_xor_se_lz, ih]
  | swap a b rest =>
    show mech_se_lz b ^^^ (mech_se_lz a ^^^ chain_xor_se_lz rest) =
         mech_se_lz a ^^^ (mech_se_lz b ^^^ chain_xor_se_lz rest)
    calc mech_se_lz b ^^^ (mech_se_lz a ^^^ chain_xor_se_lz rest)
        = (mech_se_lz b ^^^ mech_se_lz a) ^^^ chain_xor_se_lz rest := by
          rw [← BitVec.xor_assoc]
      _ = (mech_se_lz a ^^^ mech_se_lz b) ^^^ chain_xor_se_lz rest := by
          rw [BitVec.xor_comm (mech_se_lz b) (mech_se_lz a)]
      _ = mech_se_lz a ^^^ (mech_se_lz b ^^^ chain_xor_se_lz rest) := BitVec.xor_assoc _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem chain_xor_se_syn_dup (a : Fin 252) (rest : List (Fin 252)) :
    chain_xor_se_syn (a :: a :: rest) = chain_xor_se_syn rest := by
  show mech_se_syn a ^^^ (mech_se_syn a ^^^ chain_xor_se_syn rest) = chain_xor_se_syn rest
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem chain_xor_se_lz_dup (a : Fin 252) (rest : List (Fin 252)) :
    chain_xor_se_lz (a :: a :: rest) = chain_xor_se_lz rest := by
  show mech_se_lz a ^^^ (mech_se_lz a ^^^ chain_xor_se_lz rest) = chain_xor_se_lz rest
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end QStab.Paper.BB72BVSE
