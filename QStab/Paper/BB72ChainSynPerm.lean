import QStab.Paper.BB72SynBridge

/-!
# Permutation invariance and duplicate cancellation for chain syndromes

Two abstract lemmas about `chain_xor_syn` and `chain_xor_lz`:
  * **Permutation invariance**: `c ~ c' → chain_xor_syn c = chain_xor_syn c'`
  * **Duplicate cancellation**: `chain_xor_syn (a :: a :: rest) = chain_xor_syn rest`

These are the building blocks for reducing arbitrary K-chains to sorted
distinct K'-chains (with K' ≤ K, same parity).
-/

open List

namespace QStab.Paper.BB72BV

/-! ## Permutation invariance -/

theorem chain_xor_syn_perm {c c' : List (Fin 252)} (h : c ~ c') :
    chain_xor_syn c = chain_xor_syn c' := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [chain_xor_syn, ih]
  | swap a b rest =>
    -- swap: Perm (b :: a :: rest) (a :: b :: rest)
    show mech_syn b ^^^ (mech_syn a ^^^ chain_xor_syn rest) =
         mech_syn a ^^^ (mech_syn b ^^^ chain_xor_syn rest)
    calc mech_syn b ^^^ (mech_syn a ^^^ chain_xor_syn rest)
        = (mech_syn b ^^^ mech_syn a) ^^^ chain_xor_syn rest := by
          rw [← BitVec.xor_assoc]
      _ = (mech_syn a ^^^ mech_syn b) ^^^ chain_xor_syn rest := by
          rw [BitVec.xor_comm (mech_syn b) (mech_syn a)]
      _ = mech_syn a ^^^ (mech_syn b ^^^ chain_xor_syn rest) := BitVec.xor_assoc _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem chain_xor_lz_perm {c c' : List (Fin 252)} (h : c ~ c') :
    chain_xor_lz c = chain_xor_lz c' := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [chain_xor_lz, ih]
  | swap a b rest =>
    show mech_lz b ^^^ (mech_lz a ^^^ chain_xor_lz rest) =
         mech_lz a ^^^ (mech_lz b ^^^ chain_xor_lz rest)
    calc mech_lz b ^^^ (mech_lz a ^^^ chain_xor_lz rest)
        = (mech_lz b ^^^ mech_lz a) ^^^ chain_xor_lz rest := by
          rw [← BitVec.xor_assoc]
      _ = (mech_lz a ^^^ mech_lz b) ^^^ chain_xor_lz rest := by
          rw [BitVec.xor_comm (mech_lz b) (mech_lz a)]
      _ = mech_lz a ^^^ (mech_lz b ^^^ chain_xor_lz rest) := BitVec.xor_assoc _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Duplicate cancellation -/

theorem chain_xor_syn_dup (a : Fin 252) (rest : List (Fin 252)) :
    chain_xor_syn (a :: a :: rest) = chain_xor_syn rest := by
  show mech_syn a ^^^ (mech_syn a ^^^ chain_xor_syn rest) = chain_xor_syn rest
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem chain_xor_lz_dup (a : Fin 252) (rest : List (Fin 252)) :
    chain_xor_lz (a :: a :: rest) = chain_xor_lz rest := by
  show mech_lz a ^^^ (mech_lz a ^^^ chain_xor_lz rest) = chain_xor_lz rest
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end QStab.Paper.BB72BV
