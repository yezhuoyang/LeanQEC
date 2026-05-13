import QStab.Paper.BB72SEChainSynPerm
import QStab.Paper.BB72ChainListReduce

open List

namespace QStab.Paper.BB72BVSE

theorem chain_xor_se_syn_cons_mem (a : Fin 252) (rest : List (Fin 252)) (h : a ∈ rest) :
    chain_xor_se_syn (a :: rest) = chain_xor_se_syn (rest.erase a) := by
  have hperm : rest ~ a :: (rest.erase a) := List.perm_cons_erase h
  have hperm2 : (a :: rest) ~ (a :: a :: (rest.erase a)) := List.Perm.cons a hperm
  rw [chain_xor_se_syn_perm hperm2, chain_xor_se_syn_dup]

theorem chain_xor_se_lz_cons_mem (a : Fin 252) (rest : List (Fin 252)) (h : a ∈ rest) :
    chain_xor_se_lz (a :: rest) = chain_xor_se_lz (rest.erase a) := by
  have hperm : rest ~ a :: (rest.erase a) := List.perm_cons_erase h
  have hperm2 : (a :: rest) ~ (a :: a :: (rest.erase a)) := List.Perm.cons a hperm
  rw [chain_xor_se_lz_perm hperm2, chain_xor_se_lz_dup]

theorem chain_xor_se_syn_reduce (c : List (Fin 252)) :
    chain_xor_se_syn (QStab.Paper.BB72BV.reduce c) = chain_xor_se_syn c := by
  induction c with
  | nil => rfl
  | cons head tail ih =>
    unfold QStab.Paper.BB72BV.reduce
    by_cases hh : head ∈ QStab.Paper.BB72BV.reduce tail
    · simp [hh]
      rw [← chain_xor_se_syn_cons_mem head (QStab.Paper.BB72BV.reduce tail) hh]
      show mech_se_syn head ^^^ chain_xor_se_syn (QStab.Paper.BB72BV.reduce tail) =
           mech_se_syn head ^^^ chain_xor_se_syn tail
      rw [ih]
    · simp [hh]
      show mech_se_syn head ^^^ chain_xor_se_syn (QStab.Paper.BB72BV.reduce tail) =
           mech_se_syn head ^^^ chain_xor_se_syn tail
      rw [ih]

theorem chain_xor_se_lz_reduce (c : List (Fin 252)) :
    chain_xor_se_lz (QStab.Paper.BB72BV.reduce c) = chain_xor_se_lz c := by
  induction c with
  | nil => rfl
  | cons head tail ih =>
    unfold QStab.Paper.BB72BV.reduce
    by_cases hh : head ∈ QStab.Paper.BB72BV.reduce tail
    · simp [hh]
      rw [← chain_xor_se_lz_cons_mem head (QStab.Paper.BB72BV.reduce tail) hh]
      show mech_se_lz head ^^^ chain_xor_se_lz (QStab.Paper.BB72BV.reduce tail) =
           mech_se_lz head ^^^ chain_xor_se_lz tail
      rw [ih]
    · simp [hh]
      show mech_se_lz head ^^^ chain_xor_se_lz (QStab.Paper.BB72BV.reduce tail) =
           mech_se_lz head ^^^ chain_xor_se_lz tail
      rw [ih]

end QStab.Paper.BB72BVSE
