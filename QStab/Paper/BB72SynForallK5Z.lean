import QStab.Paper.BB72SynVerifyZ

/-!
# Z-side K=5 sorted forall via List.any with `List.drop` skipping

Mirror of `BB72SynForallK5`. Build cost ~145 min (vs ~94 min for the
Id.run existence form already in `BB72SynVerifyZ`).
-/

namespace QStab.Paper.BB72BVZ

def k5_sorted_attack_exists_Z : Bool :=
  (List.finRange 252).any fun i =>
    ((List.finRange 252).drop (i.val + 1)).any fun j =>
      ((List.finRange 252).drop (j.val + 1)).any fun k =>
        ((List.finRange 252).drop (k.val + 1)).any fun l =>
          ((List.finRange 252).drop (l.val + 1)).any fun m =>
            decide (mech_xstab_syn i ^^^ mech_xstab_syn j ^^^ mech_xstab_syn k ^^^
                    mech_xstab_syn l ^^^ mech_xstab_syn m = 0) &&
            decide (mech_lx i ^^^ mech_lx j ^^^ mech_lx k ^^^
                    mech_lx l ^^^ mech_lx m ≠ 0)

theorem k5_sorted_attack_exists_Z_eq_false : k5_sorted_attack_exists_Z = false := by
  native_decide

end QStab.Paper.BB72BVZ
