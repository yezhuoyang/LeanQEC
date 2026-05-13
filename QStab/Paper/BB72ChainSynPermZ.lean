import QStab.Paper.BB72SynBridgeZ

/-!
# Permutation invariance and duplicate cancellation for Z-side chain syndromes

Mirror of `BB72ChainSynPerm` for the Z-side (`chain_xor_syn_Z`, `chain_xor_lx`).
-/

open List

namespace QStab.Paper.BB72BVZ

theorem chain_xor_syn_Z_perm {c c' : List (Fin 252)} (h : c ~ c') :
    chain_xor_syn_Z c = chain_xor_syn_Z c' := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [chain_xor_syn_Z, ih]
  | swap a b rest =>
    show mech_xstab_syn b ^^^ (mech_xstab_syn a ^^^ chain_xor_syn_Z rest) =
         mech_xstab_syn a ^^^ (mech_xstab_syn b ^^^ chain_xor_syn_Z rest)
    calc mech_xstab_syn b ^^^ (mech_xstab_syn a ^^^ chain_xor_syn_Z rest)
        = (mech_xstab_syn b ^^^ mech_xstab_syn a) ^^^ chain_xor_syn_Z rest := by
          rw [← BitVec.xor_assoc]
      _ = (mech_xstab_syn a ^^^ mech_xstab_syn b) ^^^ chain_xor_syn_Z rest := by
          rw [BitVec.xor_comm (mech_xstab_syn b) (mech_xstab_syn a)]
      _ = mech_xstab_syn a ^^^ (mech_xstab_syn b ^^^ chain_xor_syn_Z rest) := BitVec.xor_assoc _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem chain_xor_lx_perm {c c' : List (Fin 252)} (h : c ~ c') :
    chain_xor_lx c = chain_xor_lx c' := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [chain_xor_lx, ih]
  | swap a b rest =>
    show mech_lx b ^^^ (mech_lx a ^^^ chain_xor_lx rest) =
         mech_lx a ^^^ (mech_lx b ^^^ chain_xor_lx rest)
    calc mech_lx b ^^^ (mech_lx a ^^^ chain_xor_lx rest)
        = (mech_lx b ^^^ mech_lx a) ^^^ chain_xor_lx rest := by
          rw [← BitVec.xor_assoc]
      _ = (mech_lx a ^^^ mech_lx b) ^^^ chain_xor_lx rest := by
          rw [BitVec.xor_comm (mech_lx b) (mech_lx a)]
      _ = mech_lx a ^^^ (mech_lx b ^^^ chain_xor_lx rest) := BitVec.xor_assoc _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem chain_xor_syn_Z_dup (a : Fin 252) (rest : List (Fin 252)) :
    chain_xor_syn_Z (a :: a :: rest) = chain_xor_syn_Z rest := by
  show mech_xstab_syn a ^^^ (mech_xstab_syn a ^^^ chain_xor_syn_Z rest) = chain_xor_syn_Z rest
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem chain_xor_lx_dup (a : Fin 252) (rest : List (Fin 252)) :
    chain_xor_lx (a :: a :: rest) = chain_xor_lx rest := by
  show mech_lx a ^^^ (mech_lx a ^^^ chain_xor_lx rest) = chain_xor_lx rest
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end QStab.Paper.BB72BVZ
