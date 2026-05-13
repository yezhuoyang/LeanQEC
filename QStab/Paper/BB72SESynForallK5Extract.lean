import QStab.Paper.BB72SESynForallK5

namespace QStab.Paper.BB72BVSE

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

theorem no_5_chain_attack_sorted_SE :
    ∀ (i j k l m : Fin 252), i.val < j.val → j.val < k.val → k.val < l.val → l.val < m.val →
      ¬ (mech_se_syn i ^^^ mech_se_syn j ^^^ mech_se_syn k ^^^
         mech_se_syn l ^^^ mech_se_syn m = 0 ∧
         mech_se_lz i ^^^ mech_se_lz j ^^^ mech_se_lz k ^^^ mech_se_lz l ^^^ mech_se_lz m ≠ 0) := by
  intro i j k l m hij hjk hkl hlm hatt
  have hexists : k5_sorted_attack_exists_SE = true := by
    unfold k5_sorted_attack_exists_SE
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
  rw [k5_sorted_attack_exists_SE_eq_false] at hexists
  exact Bool.false_ne_true hexists

end QStab.Paper.BB72BVSE
