import QStab.Paper.BB72SynVerifyZ

/-!
# Z-side K=1, K=3, K=4 forall-form no-attack

Mirror of `BB72SynForallK13` and `BB72SynForall`. Proven via direct
`native_decide` on the explicit forall.

Build cost estimates: K=1 trivial, K=3 ~1 min, K=4 ~100s.
-/

namespace QStab.Paper.BB72BVZ

/-- **No 1-tuple Z-mech is a Z-side attack** (forall). -/
theorem no_1_chain_attack_Z :
    ∀ (a : Fin 252),
      ¬ (mech_xstab_syn a = 0 ∧ mech_lx a ≠ 0) := by
  native_decide

/-- **No sorted distinct 3-tuple of Z-mechs is an attack** (forall). -/
theorem no_3_chain_attack_sorted_Z :
    ∀ (i j k : Fin 252), i.val < j.val → j.val < k.val →
      ¬ (mech_xstab_syn i ^^^ mech_xstab_syn j ^^^ mech_xstab_syn k = 0 ∧
         mech_lx i ^^^ mech_lx j ^^^ mech_lx k ≠ 0) := by
  native_decide

/-- **No sorted distinct 4-tuple of Z-mechs is an attack** (forall). -/
theorem no_4_chain_attack_sorted_Z :
    ∀ (i j k l : Fin 252), i.val < j.val → j.val < k.val → k.val < l.val →
      ¬ (mech_xstab_syn i ^^^ mech_xstab_syn j ^^^ mech_xstab_syn k ^^^ mech_xstab_syn l = 0 ∧
         mech_lx i ^^^ mech_lx j ^^^ mech_lx k ^^^ mech_lx l ≠ 0) := by
  native_decide

end QStab.Paper.BB72BVZ
