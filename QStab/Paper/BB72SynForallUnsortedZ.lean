import QStab.Paper.BB72SynVerifyZ

/-!
# Z-side K=4 unsorted forall (for handling arbitrary 4-tuples)

Mirror of `BB72SynForallUnsorted`. Proves the K=4 forall over all 252⁴
ordered 4-tuples (any order, any duplicates) via direct `native_decide`.

Build cost: ~97 min (similar to X-side K=4 unsorted timing).
-/

namespace QStab.Paper.BB72BVZ

/-- **No 4-tuple of Z-mechs is an attack** (unsorted, allows duplicates). -/
theorem no_4_chain_attack_unsorted_Z :
    ∀ (i j k l : Fin 252),
      ¬ (mech_xstab_syn i ^^^ mech_xstab_syn j ^^^ mech_xstab_syn k ^^^ mech_xstab_syn l = 0 ∧
         mech_lx i ^^^ mech_lx j ^^^ mech_lx k ^^^ mech_lx l ≠ 0) := by
  native_decide

end QStab.Paper.BB72BVZ
