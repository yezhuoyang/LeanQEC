import QStab.Paper.BB72SESynVerify

namespace QStab.Paper.BB72BVSE

/-- K=5 sorted distinct attack-existence via `List.any` with `drop` skipping. -/
def k5_sorted_attack_exists_SE : Bool :=
  (List.finRange 252).any fun i =>
    ((List.finRange 252).drop (i.val + 1)).any fun j =>
      ((List.finRange 252).drop (j.val + 1)).any fun k =>
        ((List.finRange 252).drop (k.val + 1)).any fun l =>
          ((List.finRange 252).drop (l.val + 1)).any fun m =>
            decide (mech_se_syn i ^^^ mech_se_syn j ^^^ mech_se_syn k ^^^
                    mech_se_syn l ^^^ mech_se_syn m = 0) &&
            decide (mech_se_lz i ^^^ mech_se_lz j ^^^ mech_se_lz k ^^^
                    mech_se_lz l ^^^ mech_se_lz m ≠ 0)

theorem k5_sorted_attack_exists_SE_eq_false : k5_sorted_attack_exists_SE = false := by
  native_decide

end QStab.Paper.BB72BVSE
