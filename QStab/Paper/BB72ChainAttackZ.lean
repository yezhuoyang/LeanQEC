import QStab.Paper.BB72SynBridgeZ
import QStab.Paper.BB72ChainCheckZ

/-!
# Z-side chain attack: K=0,1,2,3 small cases

Mirror of `BB72ChainAttack` for Z-side. Discharges length-0..3 chains
directly via small SAT (k=1,2 in `BB72ChainCheckZ`) plus a K=3 native_decide.
-/

namespace QStab.Paper.BB72BVZ

open QStab QStab.Paper.BB72JointInstance QStab.Paper.BB72ReachableEBridgeZ
  QStab.Paper.BB72ChainCheckZ

@[simp] theorem chain_xor_Z_singleton (i : Fin 252) :
    chain_xor_Z [i] = bb_zMech i := by
  unfold chain_xor_Z
  show ErrorVec.mul (bb_zMech i) (ErrorVec.identity 72) = bb_zMech i
  unfold ErrorVec.mul ErrorVec.identity
  funext q
  generalize bb_zMech i q = p
  cases p <;> rfl

theorem bb_chain_attack_Z_k0 :
    ∀ chain : List (Fin 252), chain.length = 0 →
      bb_chain_attack_Z chain = false := by
  intro chain h
  rw [List.length_eq_zero_iff] at h
  rw [h]
  unfold bb_chain_attack_Z chain_xor_Z bb_isSuccessZside
  simp [ErrorVec.parity_identity]

theorem bb_chain_attack_Z_k1 :
    ∀ chain : List (Fin 252), chain.length = 1 →
      bb_chain_attack_Z chain = false := by
  intro chain h
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp h
  unfold bb_chain_attack_Z
  rw [chain_xor_Z_singleton]
  exact bb_chain_1_no_attack_Z i

@[simp] theorem chain_xor_Z_pair (i j : Fin 252) :
    chain_xor_Z [i, j] = ErrorVec.mul (bb_zMech i) (bb_zMech j) := by
  show ErrorVec.mul (bb_zMech i) (chain_xor_Z [j]) = _
  rw [chain_xor_Z_singleton]

theorem bb_chain_attack_Z_k2 :
    ∀ chain : List (Fin 252), chain.length = 2 →
      bb_chain_attack_Z chain = false := by
  intro chain h
  match chain, h with
  | [i, j], _ =>
    unfold bb_chain_attack_Z
    rw [chain_xor_Z_pair]
    exact bb_chain_2_no_attack_Z i j

/-- **No length-3 Z-chain is a successful Z-side attack.**
    Discharged via the syndrome bridge plus `no_3_chain_attack_sorted_Z`,
    composed via reduce/sort for unsorted/duplicate triples.

    Direct path: native_decide on the syndrome form for arbitrary (i, j, k).
    Build cost: 252^3 = 16M cases, ~1 min. -/
theorem bb_chain_attack_Z_k3_syn :
    ∀ (i j k : Fin 252),
      ¬ (mech_xstab_syn i ^^^ mech_xstab_syn j ^^^ mech_xstab_syn k = 0 ∧
         mech_lx i ^^^ mech_lx j ^^^ mech_lx k ≠ 0) := by
  native_decide

theorem bb_chain_attack_Z_k3 :
    ∀ chain : List (Fin 252), chain.length = 3 →
      bb_chain_attack_Z chain = false := by
  intro chain h
  match chain, h with
  | [i, j, k], _ =>
    by_contra hatt
    rw [Bool.not_eq_false] at hatt
    obtain ⟨hsyn, hlx⟩ := (bb_chain_attack_Z_iff_syn _).mp hatt
    apply bb_chain_attack_Z_k3_syn i j k
    refine ⟨?_, ?_⟩
    · have h1 : chain_xor_syn_Z [i, j, k] =
          mech_xstab_syn i ^^^ mech_xstab_syn j ^^^ mech_xstab_syn k := by
        show mech_xstab_syn i ^^^ (mech_xstab_syn j ^^^ (mech_xstab_syn k ^^^ 0)) = _
        simp [BitVec.xor_assoc]
      rw [← h1]; exact hsyn
    · have h2 : chain_xor_lx [i, j, k] =
          mech_lx i ^^^ mech_lx j ^^^ mech_lx k := by
        show mech_lx i ^^^ (mech_lx j ^^^ (mech_lx k ^^^ 0)) = _
        simp [BitVec.xor_assoc]
      rw [← h2]; exact hlx

end QStab.Paper.BB72BVZ
