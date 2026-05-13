import QStab.Paper.BB72SynForallK5

/-!
# Extract the K=5 sorted forall from `k5_sorted_attack_exists_eq_false`

The Bool theorem `k5_sorted_attack_exists_eq_false` says the nested
`List.any` chain returns `false`. Via `List.any_eq_true`, this gives:
no witness in any of the 5 nested lists makes the inner predicate true.

Combined with the membership conditions, this yields the sorted forall.
-/

namespace QStab.Paper.BB72BV

/-- Helper: for `j : Fin n`, `j ∈ (List.finRange n).drop k ↔ j.val ≥ k`. -/
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

/-- **K=5 sorted distinct forall: no attack** (extracted from List.any). -/
theorem no_5_chain_attack_sorted :
    ∀ (i j k l m : Fin 252), i.val < j.val → j.val < k.val → k.val < l.val → l.val < m.val →
      ¬ (mech_syn i ^^^ mech_syn j ^^^ mech_syn k ^^^ mech_syn l ^^^ mech_syn m = 0 ∧
         mech_lz i ^^^ mech_lz j ^^^ mech_lz k ^^^ mech_lz l ^^^ mech_lz m ≠ 0) := by
  intro i j k l m hij hjk hkl hlm hatt
  have hexists : k5_sorted_attack_exists = true := by
    unfold k5_sorted_attack_exists
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
    -- Inner predicate: decide (syn = 0) && decide (lz ≠ 0) = true
    rw [decide_eq_true hatt.1, decide_eq_true hatt.2]
    rfl
  -- contradiction: hexists says true, k5_sorted_attack_exists_eq_false says false
  rw [k5_sorted_attack_exists_eq_false] at hexists
  exact Bool.false_ne_true hexists

end QStab.Paper.BB72BV
