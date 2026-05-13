import QStab.Paper.BB72ChainSynPermZ
import QStab.Paper.BB72ChainListReduce

/-!
# List reduction for Z-side chain syndromes

Reuses the X-side `reduce` function (in namespace `QStab.Paper.BB72BV`)
since it is purely a list operation on `List (Fin 252)`. Adds Z-side
invariance lemmas.
-/

open List

namespace QStab.Paper.BB72BVZ

/-! ## Cons-cancel via permutation -/

theorem chain_xor_syn_Z_cons_mem (a : Fin 252) (rest : List (Fin 252)) (h : a ∈ rest) :
    chain_xor_syn_Z (a :: rest) = chain_xor_syn_Z (rest.erase a) := by
  have hperm : rest ~ a :: (rest.erase a) := List.perm_cons_erase h
  have hperm2 : (a :: rest) ~ (a :: a :: (rest.erase a)) := List.Perm.cons a hperm
  rw [chain_xor_syn_Z_perm hperm2, chain_xor_syn_Z_dup]

theorem chain_xor_lx_cons_mem (a : Fin 252) (rest : List (Fin 252)) (h : a ∈ rest) :
    chain_xor_lx (a :: rest) = chain_xor_lx (rest.erase a) := by
  have hperm : rest ~ a :: (rest.erase a) := List.perm_cons_erase h
  have hperm2 : (a :: rest) ~ (a :: a :: (rest.erase a)) := List.Perm.cons a hperm
  rw [chain_xor_lx_perm hperm2, chain_xor_lx_dup]

/-! ## Z-side reduce invariance theorems

Reuses `QStab.Paper.BB72BV.reduce` (the function is generic over List (Fin 252)). -/

theorem chain_xor_syn_Z_reduce (c : List (Fin 252)) :
    chain_xor_syn_Z (QStab.Paper.BB72BV.reduce c) = chain_xor_syn_Z c := by
  induction c with
  | nil => rfl
  | cons head tail ih =>
    unfold QStab.Paper.BB72BV.reduce
    by_cases hh : head ∈ QStab.Paper.BB72BV.reduce tail
    · simp [hh]
      rw [← chain_xor_syn_Z_cons_mem head (QStab.Paper.BB72BV.reduce tail) hh]
      show mech_xstab_syn head ^^^ chain_xor_syn_Z (QStab.Paper.BB72BV.reduce tail) =
           mech_xstab_syn head ^^^ chain_xor_syn_Z tail
      rw [ih]
    · simp [hh]
      show mech_xstab_syn head ^^^ chain_xor_syn_Z (QStab.Paper.BB72BV.reduce tail) =
           mech_xstab_syn head ^^^ chain_xor_syn_Z tail
      rw [ih]

theorem chain_xor_lx_reduce (c : List (Fin 252)) :
    chain_xor_lx (QStab.Paper.BB72BV.reduce c) = chain_xor_lx c := by
  induction c with
  | nil => rfl
  | cons head tail ih =>
    unfold QStab.Paper.BB72BV.reduce
    by_cases hh : head ∈ QStab.Paper.BB72BV.reduce tail
    · simp [hh]
      rw [← chain_xor_lx_cons_mem head (QStab.Paper.BB72BV.reduce tail) hh]
      show mech_lx head ^^^ chain_xor_lx (QStab.Paper.BB72BV.reduce tail) =
           mech_lx head ^^^ chain_xor_lx tail
      rw [ih]
    · simp [hh]
      show mech_lx head ^^^ chain_xor_lx (QStab.Paper.BB72BV.reduce tail) =
           mech_lx head ^^^ chain_xor_lx tail
      rw [ih]

end QStab.Paper.BB72BVZ
