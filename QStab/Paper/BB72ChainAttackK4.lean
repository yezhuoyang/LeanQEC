import QStab.Paper.BB72SynForall
import QStab.Paper.BB72SynForallUnsorted
import QStab.Paper.BB72SynBridge
import QStab.Paper.BB72ChainAttack

/-!
# BB72 K=4 chain attack discharge (sorted distinct case)

Combines:
  * `no_4_chain_attack_sorted` (K=4 forall, native_decide)
  * `bb_chain_attack_iff_syn` (the structural bridge)
to discharge `bb_chain_attack` for sorted distinct 4-element chains.
-/

open QStab.Paper.BB72BV
open QStab.Paper.BB72ChainAttack

namespace QStab.Paper.BB72ChainAttackK4

/-- For sorted distinct 4-element chains, `bb_chain_attack` is `false`. -/
theorem bb_chain_attack_4_sorted_distinct
    (i j k l : Fin 252) (hij : i.val < j.val) (hjk : j.val < k.val)
    (hkl : k.val < l.val) :
    bb_chain_attack [i, j, k, l] = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  obtain ⟨hsyn, hlz⟩ := (bb_chain_attack_iff_syn _).mp h
  apply no_4_chain_attack_sorted i j k l hij hjk hkl
  refine ⟨?_, ?_⟩
  · have h1 : chain_xor_syn [i, j, k, l] =
        mech_syn i ^^^ mech_syn j ^^^ mech_syn k ^^^ mech_syn l := by
      show mech_syn i ^^^ (mech_syn j ^^^ (mech_syn k ^^^ (mech_syn l ^^^ 0))) = _
      simp [BitVec.xor_assoc]
    rw [← h1]; exact hsyn
  · have h2 : chain_xor_lz [i, j, k, l] =
        mech_lz i ^^^ mech_lz j ^^^ mech_lz k ^^^ mech_lz l := by
      show mech_lz i ^^^ (mech_lz j ^^^ (mech_lz k ^^^ (mech_lz l ^^^ 0))) = _
      simp [BitVec.xor_assoc]
    rw [← h2]; exact hlz

/-- **No 4-element chain is a successful X-side attack** (any order, any duplicates).
    The unsorted forall version covers all 252⁴ tuples. -/
theorem bb_chain_attack_k4 :
    ∀ chain : List (Fin 252), chain.length = 4 →
      bb_chain_attack chain = false := by
  intro chain h
  match chain, h with
  | [a, b, c, d], _ =>
    by_contra hatt
    rw [Bool.not_eq_false] at hatt
    obtain ⟨hsyn, hlz⟩ := (bb_chain_attack_iff_syn _).mp hatt
    apply no_4_chain_attack_unsorted a b c d
    refine ⟨?_, ?_⟩
    · have h1 : chain_xor_syn [a, b, c, d] =
          mech_syn a ^^^ mech_syn b ^^^ mech_syn c ^^^ mech_syn d := by
        show mech_syn a ^^^ (mech_syn b ^^^ (mech_syn c ^^^ (mech_syn d ^^^ 0))) = _
        simp [BitVec.xor_assoc]
      rw [← h1]; exact hsyn
    · have h2 : chain_xor_lz [a, b, c, d] =
          mech_lz a ^^^ mech_lz b ^^^ mech_lz c ^^^ mech_lz d := by
        show mech_lz a ^^^ (mech_lz b ^^^ (mech_lz c ^^^ (mech_lz d ^^^ 0))) = _
        simp [BitVec.xor_assoc]
      rw [← h2]; exact hlz

/-- **Stronger conditional**: K=4 is now unconditional, so the composite needs
    only the K=5 hypothesis. -/
theorem bb_chain_attack_le_5_of_k5
    (h_k5 : ∀ chain : List (Fin 252), chain.length = 5 →
              bb_chain_attack chain = false) :
    ∀ chain : List (Fin 252), chain.length ≤ 5 →
      bb_chain_attack chain = false := by
  intro chain h
  match hlen : chain.length with
  | 0 => exact bb_chain_attack_k0 chain hlen
  | 1 => exact bb_chain_attack_k1 chain hlen
  | 2 => exact bb_chain_attack_k2 chain hlen
  | 3 => exact bb_chain_attack_k3 chain hlen
  | 4 => exact bb_chain_attack_k4 chain hlen
  | 5 => exact h_k5 chain hlen
  | n + 6 => omega

end QStab.Paper.BB72ChainAttackK4
