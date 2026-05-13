import QStab.Paper.BB72SynVerify

/-!
# K=1 and K=3 forall-form no-attack (sorted distinct)

For the K=5 list-reduction strategy (Option C), any length-5 chain
reduces (via permutation + duplicate cancellation) to a sorted distinct
list of length ∈ {1, 3, 5}. We need forall versions for each:

  * K=1: trivial (252 cases).
  * K=3: ~1 min via native_decide (252³ cases).
  * K=5: handled separately (see notes/k5_strategy.md).

This file proves K=1 and K=3 forall versions.
-/

namespace QStab.Paper.BB72BV

/-- **No 1-tuple is an attack** (forall). -/
theorem no_1_chain_attack :
    ∀ (a : Fin 252),
      ¬ (mech_syn a = 0 ∧ mech_lz a ≠ 0) := by
  native_decide

/-- **No sorted distinct 3-tuple is an attack** (forall). -/
theorem no_3_chain_attack_sorted :
    ∀ (i j k : Fin 252), i.val < j.val → j.val < k.val →
      ¬ (mech_syn i ^^^ mech_syn j ^^^ mech_syn k = 0 ∧
         mech_lz i ^^^ mech_lz j ^^^ mech_lz k ≠ 0) := by
  native_decide

end QStab.Paper.BB72BV
