import QStab.Paper.BB72SynVerify

/-!
# K=5 sorted forall via List.any with `List.drop` skipping

The naive `List.any` over `List.finRange 252` × 5 levels iterates 252⁵ = 1T cases,
checking `decide (i.val < j.val)` etc. for each — O(1T) constraint checks.

This file uses `(List.finRange 252).drop (i.val + 1)` to skip directly to
valid `j > i`, mirroring the Id.run for-loop's `continue` semantics.
Total cases iterated: C(252, 5) ≈ 8.1G — same as existence form.

Build cost: similar to existence form (~94 min).
Once `= false`, `List.any_eq_false_iff_forall_not` extracts the forall directly.
-/

namespace QStab.Paper.BB72BV

/-- K=5 sorted distinct attack-existence via `List.any` with `drop` skipping. -/
def k5_sorted_attack_exists : Bool :=
  (List.finRange 252).any fun i =>
    ((List.finRange 252).drop (i.val + 1)).any fun j =>
      ((List.finRange 252).drop (j.val + 1)).any fun k =>
        ((List.finRange 252).drop (k.val + 1)).any fun l =>
          ((List.finRange 252).drop (l.val + 1)).any fun m =>
            decide (mech_syn i ^^^ mech_syn j ^^^ mech_syn k ^^^
                    mech_syn l ^^^ mech_syn m = 0) &&
            decide (mech_lz i ^^^ mech_lz j ^^^ mech_lz k ^^^
                    mech_lz l ^^^ mech_lz m ≠ 0)

theorem k5_sorted_attack_exists_eq_false : k5_sorted_attack_exists = false := by
  native_decide

end QStab.Paper.BB72BV
