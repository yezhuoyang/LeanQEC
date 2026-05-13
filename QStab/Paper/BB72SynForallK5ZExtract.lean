import QStab.Paper.BB72SynForallK5Z

/-!
# Extract the Z-side K=5 sorted forall from `k5_sorted_attack_exists_Z_eq_false`
-/

namespace QStab.Paper.BB72BVZ

private theorem mem_finRange_drop {n : Nat} {k : Nat} {j : Fin n} :
    j ∈ (List.finRange n).drop k ↔ j.val ≥ k := by
  rw [List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨m, hm, hget⟩
    rw [List.getElem_finRange] at hget
    have : j.val = k + m := by
      have := congrArg Fin.val hget.symm
      simpa [Fin.cast] using this
    omega
  · intro hge
    refine ⟨j.val - k, ?_, ?_⟩
    · simp [List.length_finRange]; omega
    · rw [List.getElem_finRange]
      ext
      show k + (j.val - k) = j.val
      omega

/-- **Z-side K=5 sorted distinct forall: no attack** (extracted from List.any). -/
theorem no_5_chain_attack_sorted_Z :
    ∀ (i j k l m : Fin 252), i.val < j.val → j.val < k.val → k.val < l.val → l.val < m.val →
      ¬ (mech_xstab_syn i ^^^ mech_xstab_syn j ^^^ mech_xstab_syn k ^^^
         mech_xstab_syn l ^^^ mech_xstab_syn m = 0 ∧
         mech_lx i ^^^ mech_lx j ^^^ mech_lx k ^^^ mech_lx l ^^^ mech_lx m ≠ 0) := by
  intro i j k l m hij hjk hkl hlm hatt
  have hexists : k5_sorted_attack_exists_Z = true := by
    unfold k5_sorted_attack_exists_Z
    rw [List.any_eq_true]
    refine ⟨i, List.mem_finRange i, ?_⟩
    rw [List.any_eq_true]
    refine ⟨j, mem_finRange_drop.mpr (by omega), ?_⟩
    rw [List.any_eq_true]
    refine ⟨k, mem_finRange_drop.mpr (by omega), ?_⟩
    rw [List.any_eq_true]
    refine ⟨l, mem_finRange_drop.mpr (by omega), ?_⟩
    rw [List.any_eq_true]
    refine ⟨m, mem_finRange_drop.mpr (by omega), ?_⟩
    rw [decide_eq_true hatt.1, decide_eq_true hatt.2]
    rfl
  rw [k5_sorted_attack_exists_Z_eq_false] at hexists
  exact Bool.false_ne_true hexists

end QStab.Paper.BB72BVZ
