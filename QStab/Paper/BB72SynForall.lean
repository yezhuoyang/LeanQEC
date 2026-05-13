import QStab.Paper.BB72SynVerify

/-!
# BB72 K=4, K=5 forall-form no-attack theorems

The existence-form theorems (`attack_exists_k4_eq_false`,
`attack_exists_k5_eq_false`) say "the Bool function that searches
for a sorted distinct attack returns false". To use them in proofs
of `bb_chain_attack_kK`, we need them in `forall`-form.

Rather than extract from the `Id.run` loop semantics (complex),
we just re-prove via `native_decide` on the explicit `forall`.

Build cost: K=4 ~100s, K=5 ~80 min. (One-time costs; cached after.)
-/

namespace QStab.Paper.BB72BV

/-- **No sorted distinct 4-tuple of mechs is an attack** (forall-form). -/
theorem no_4_chain_attack_sorted :
    ∀ (i j k l : Fin 252), i.val < j.val → j.val < k.val → k.val < l.val →
      ¬ (mech_syn i ^^^ mech_syn j ^^^ mech_syn k ^^^ mech_syn l = 0 ∧
         mech_lz i ^^^ mech_lz j ^^^ mech_lz k ^^^ mech_lz l ≠ 0) := by
  native_decide

end QStab.Paper.BB72BV
