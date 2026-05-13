import QStab.Paper.BB72SynBridge
import QStab.Paper.BB72ChainAttack

/-!
# BB72 K=5 chain attack discharge (conditional on K=5 forall hypothesis)

This file documents the structural composition for K=5 chain attack
discharge, parameterized by the (currently unproven) K=5 unsorted forall.

Once K=5 unsorted forall is established (via either brute-force
native_decide ~50 hours, or abstract Lean proof), the conditional
theorem here becomes unconditional.

See `notes/k5_strategy.md` for path options.
-/

open QStab.Paper.BB72BV
open QStab.Paper.BB72ChainAttack

namespace QStab.Paper.BB72ChainAttackK5

/-- **Conditional**: assuming the K=5 unsorted forall, K=5 chain attack
    is discharged for arbitrary length-5 chains. -/
theorem bb_chain_attack_k5_of_no_5_unsorted
    (h : ∀ (a b c d e : Fin 252),
         ¬ (mech_syn a ^^^ mech_syn b ^^^ mech_syn c ^^^ mech_syn d ^^^ mech_syn e = 0 ∧
            mech_lz a ^^^ mech_lz b ^^^ mech_lz c ^^^ mech_lz d ^^^ mech_lz e ≠ 0)) :
    ∀ chain : List (Fin 252), chain.length = 5 →
      bb_chain_attack chain = false := by
  intro chain hlen
  match chain, hlen with
  | [a, b, c, d, e], _ =>
    by_contra hatt
    rw [Bool.not_eq_false] at hatt
    obtain ⟨hsyn, hlz⟩ := (bb_chain_attack_iff_syn _).mp hatt
    apply h a b c d e
    refine ⟨?_, ?_⟩
    · have h1 : chain_xor_syn [a, b, c, d, e] =
          mech_syn a ^^^ mech_syn b ^^^ mech_syn c ^^^ mech_syn d ^^^ mech_syn e := by
        show mech_syn a ^^^ (mech_syn b ^^^ (mech_syn c ^^^ (mech_syn d ^^^ (mech_syn e ^^^ 0)))) = _
        simp [BitVec.xor_assoc]
      rw [← h1]; exact hsyn
    · have h2 : chain_xor_lz [a, b, c, d, e] =
          mech_lz a ^^^ mech_lz b ^^^ mech_lz c ^^^ mech_lz d ^^^ mech_lz e := by
        show mech_lz a ^^^ (mech_lz b ^^^ (mech_lz c ^^^ (mech_lz d ^^^ (mech_lz e ^^^ 0)))) = _
        simp [BitVec.xor_assoc]
      rw [← h2]; exact hlz

end QStab.Paper.BB72ChainAttackK5
