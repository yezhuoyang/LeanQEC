import QStab.Paper.BB72SynForallUnsortedZ
import QStab.Paper.BB72ChainAttackZ

/-!
# Z-side K=4 chain attack discharge (any order, any duplicates)

Mirror of `BB72ChainAttackK4`. Uses `no_4_chain_attack_unsorted_Z`.
-/

namespace QStab.Paper.BB72ChainAttackK4Z

open QStab.Paper.BB72BVZ

/-- **No 4-element Z-chain is a successful Z-side attack** (any order, any duplicates). -/
theorem bb_chain_attack_Z_k4 :
    ∀ chain : List (Fin 252), chain.length = 4 →
      bb_chain_attack_Z chain = false := by
  intro chain h
  match chain, h with
  | [a, b, c, d], _ =>
    by_contra hatt
    rw [Bool.not_eq_false] at hatt
    obtain ⟨hsyn, hlx⟩ := (bb_chain_attack_Z_iff_syn _).mp hatt
    apply no_4_chain_attack_unsorted_Z a b c d
    refine ⟨?_, ?_⟩
    · have h1 : chain_xor_syn_Z [a, b, c, d] =
          mech_xstab_syn a ^^^ mech_xstab_syn b ^^^ mech_xstab_syn c ^^^ mech_xstab_syn d := by
        show mech_xstab_syn a ^^^ (mech_xstab_syn b ^^^ (mech_xstab_syn c ^^^ (mech_xstab_syn d ^^^ 0))) = _
        simp [BitVec.xor_assoc]
      rw [← h1]; exact hsyn
    · have h2 : chain_xor_lx [a, b, c, d] =
          mech_lx a ^^^ mech_lx b ^^^ mech_lx c ^^^ mech_lx d := by
        show mech_lx a ^^^ (mech_lx b ^^^ (mech_lx c ^^^ (mech_lx d ^^^ 0))) = _
        simp [BitVec.xor_assoc]
      rw [← h2]; exact hlx

end QStab.Paper.BB72ChainAttackK4Z
