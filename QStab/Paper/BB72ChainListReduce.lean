import QStab.Paper.BB72ChainSynPerm

/-!
# List reduction: any chain reduces to a sorted distinct subset

For chain c of length n, we want a sorted distinct list c' such that
chain_xor_syn c = chain_xor_syn c' and chain_xor_lz c = chain_xor_lz c',
with c'.length having the same parity as n and ≤ n.

This file builds the list-reduction infrastructure used to discharge
`bb_chain_attack_kK` for arbitrary chains (any order, any duplicates)
from the `sorted distinct K-tuple` forall versions.

## Strategy

For chain `c`, define `oddSupp c : Finset (Fin 252)` = elements appearing
odd number of times. Equivalently, the chain XOR is determined by oddSupp.

  chain_xor_syn c = ∑_{i ∈ oddSupp c} mech_syn i  (XOR-sum)

This is a direct consequence of permutation invariance + duplicate
cancellation.
-/

open List

namespace QStab.Paper.BB72BV

/-! ## Key lemma: cons-cancel via permutation -/

/-- If `a` appears in `rest`, then `chain_xor_syn (a :: rest) = chain_xor_syn (rest.erase a)`. -/
theorem chain_xor_syn_cons_mem (a : Fin 252) (rest : List (Fin 252)) (h : a ∈ rest) :
    chain_xor_syn (a :: rest) = chain_xor_syn (rest.erase a) := by
  -- rest = (rest.erase a) ++ ... but we need a permutation argument.
  -- Actually: rest ~ a :: (rest.erase a) when a ∈ rest.
  have hperm : rest ~ a :: (rest.erase a) := List.perm_cons_erase h
  -- So: a :: rest ~ a :: a :: (rest.erase a)
  have hperm2 : (a :: rest) ~ (a :: a :: (rest.erase a)) := List.Perm.cons a hperm
  rw [chain_xor_syn_perm hperm2, chain_xor_syn_dup]

theorem chain_xor_lz_cons_mem (a : Fin 252) (rest : List (Fin 252)) (h : a ∈ rest) :
    chain_xor_lz (a :: rest) = chain_xor_lz (rest.erase a) := by
  have hperm : rest ~ a :: (rest.erase a) := List.perm_cons_erase h
  have hperm2 : (a :: rest) ~ (a :: a :: (rest.erase a)) := List.Perm.cons a hperm
  rw [chain_xor_lz_perm hperm2, chain_xor_lz_dup]

/-! ## The reduce function: cancel duplicates to get a Nodup list with same XOR -/

/-- Reduce a chain by canceling pairs of duplicates. Result has no duplicates
    and the same `chain_xor_syn` and `chain_xor_lz`. -/
def reduce : List (Fin 252) → List (Fin 252)
  | [] => []
  | a :: rest =>
    let rs := reduce rest
    if a ∈ rs then rs.erase a
    else a :: rs

/-- `reduce c` has no duplicates. -/
theorem reduce_nodup (c : List (Fin 252)) : (reduce c).Nodup := by
  induction c with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
    show (if head ∈ reduce tail then (reduce tail).erase head else head :: reduce tail).Nodup
    by_cases hh : head ∈ reduce tail
    · rw [if_pos hh]; exact ih.erase head
    · rw [if_neg hh]; exact List.nodup_cons.mpr ⟨hh, ih⟩

/-- `chain_xor_syn` is preserved under `reduce`. -/
theorem chain_xor_syn_reduce (c : List (Fin 252)) :
    chain_xor_syn (reduce c) = chain_xor_syn c := by
  induction c with
  | nil => rfl
  | cons head tail ih =>
    unfold reduce
    by_cases hh : head ∈ reduce tail
    · simp [hh]
      -- Goal: chain_xor_syn ((reduce tail).erase head) = chain_xor_syn (head :: tail)
      rw [← chain_xor_syn_cons_mem head (reduce tail) hh]
      -- Now: chain_xor_syn (head :: reduce tail) = chain_xor_syn (head :: tail)
      show mech_syn head ^^^ chain_xor_syn (reduce tail) = mech_syn head ^^^ chain_xor_syn tail
      rw [ih]
    · simp [hh]
      show mech_syn head ^^^ chain_xor_syn (reduce tail) = mech_syn head ^^^ chain_xor_syn tail
      rw [ih]

/-- `chain_xor_lz` is preserved under `reduce`. -/
theorem chain_xor_lz_reduce (c : List (Fin 252)) :
    chain_xor_lz (reduce c) = chain_xor_lz c := by
  induction c with
  | nil => rfl
  | cons head tail ih =>
    unfold reduce
    by_cases hh : head ∈ reduce tail
    · simp [hh]
      rw [← chain_xor_lz_cons_mem head (reduce tail) hh]
      show mech_lz head ^^^ chain_xor_lz (reduce tail) = mech_lz head ^^^ chain_xor_lz tail
      rw [ih]
    · simp [hh]
      show mech_lz head ^^^ chain_xor_lz (reduce tail) = mech_lz head ^^^ chain_xor_lz tail
      rw [ih]

/-- `reduce c` has length ≤ c.length. -/
theorem reduce_length_le (c : List (Fin 252)) : (reduce c).length ≤ c.length := by
  induction c with
  | nil => exact le_refl 0
  | cons head tail ih =>
    unfold reduce
    by_cases hh : head ∈ reduce tail
    · simp [hh]
      have hle : ((reduce tail).erase head).length ≤ (reduce tail).length :=
        List.length_erase_le
      omega
    · simp [hh]
      omega

/-- `reduce c |>.length` has the same parity as `c.length`. -/
theorem reduce_length_parity (c : List (Fin 252)) :
    (reduce c).length % 2 = c.length % 2 := by
  induction c with
  | nil => rfl
  | cons head tail ih =>
    unfold reduce
    by_cases hh : head ∈ reduce tail
    · simp [hh]
      have hlen : ((reduce tail).erase head).length + 1 = (reduce tail).length :=
        List.length_erase_add_one hh
      omega
    · simp [hh]
      omega

end QStab.Paper.BB72BV
