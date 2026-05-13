import QStab.Paper.BB72SynVerify

/-!
# BB72 K=4 unsorted forall no-attack

Generalizes `no_4_chain_attack_sorted` to allow any 4-tuple (i, j, k, l)
without ordering constraints. This handles permutations and duplicates
in one shot for the K=4 case.

Proof: native_decide over Fin 252^4 = ~4G cases (including duplicate cases
which trivially fail by XOR cancellation: a chain with `a = b` reduces
to a 2-mech chain in syndrome XOR, which is already proven not to attack).

Build cost: ~50-60 min (similar to sorted forall).
-/

namespace QStab.Paper.BB72BV

/-- **No 4-tuple of mechs is an attack** (unsorted forall, includes duplicates). -/
theorem no_4_chain_attack_unsorted :
    ∀ (a b c d : Fin 252),
      ¬ (mech_syn a ^^^ mech_syn b ^^^ mech_syn c ^^^ mech_syn d = 0 ∧
         mech_lz a ^^^ mech_lz b ^^^ mech_lz c ^^^ mech_lz d ≠ 0) := by
  native_decide

end QStab.Paper.BB72BV
