import QStab.Paper.BB72ChainListReduceZ
import QStab.Paper.BB72SynForallZ
import QStab.Paper.BB72SynForallK5ZExtract
import QStab.Paper.BB72ChainAttackK4Z

/-!
# Full Z-side chain attack discharge for arbitrary length-5 chains

Mirror of `BB72ChainAttackFull` for the Z-side.
-/

open List

namespace QStab.Paper.BB72ChainAttackFullZ

open QStab.Paper.BB72BVZ
open QStab.Paper.BB72ReachableEBridgeZ

/-! ## Length-1 reduced chain discharge -/

private theorem nodup_length_1 (l : List (Fin 252)) (h : l.length = 1) :
    ∃ a, l = [a] := by
  match l, h with
  | [a], _ => exact ⟨a, rfl⟩

theorem discharge_length_1_Z (chain : List (Fin 252))
    (hchain_syn : chain_xor_syn_Z chain = 0)
    (hchain_lx : chain_xor_lx chain ≠ 0)
    (hreduce_len : (QStab.Paper.BB72BV.reduce chain).length = 1) : False := by
  obtain ⟨a, ha⟩ := nodup_length_1 (QStab.Paper.BB72BV.reduce chain) hreduce_len
  have hsyn_red : chain_xor_syn_Z (QStab.Paper.BB72BV.reduce chain) = 0 := by
    rw [chain_xor_syn_Z_reduce]; exact hchain_syn
  rw [ha] at hsyn_red
  have h1 : chain_xor_syn_Z [a] = mech_xstab_syn a := by
    show mech_xstab_syn a ^^^ 0 = mech_xstab_syn a
    exact BitVec.xor_zero
  rw [h1] at hsyn_red
  have hlx_red : chain_xor_lx (QStab.Paper.BB72BV.reduce chain) ≠ 0 := by
    rw [chain_xor_lx_reduce]; exact hchain_lx
  rw [ha] at hlx_red
  have h2 : chain_xor_lx [a] = mech_lx a := by
    show mech_lx a ^^^ 0 = mech_lx a
    exact BitVec.xor_zero
  rw [h2] at hlx_red
  exact no_1_chain_attack_Z a ⟨hsyn_red, hlx_red⟩

/-! ## Length-3 reduced chain discharge -/

private theorem xor3_acb {n} (a b c : BitVec n) : a ^^^ c ^^^ b = a ^^^ b ^^^ c := by
  rw [BitVec.xor_assoc a c b, BitVec.xor_comm c b, ← BitVec.xor_assoc a b c]
private theorem xor3_bac {n} (a b c : BitVec n) : b ^^^ a ^^^ c = a ^^^ b ^^^ c := by
  rw [BitVec.xor_comm b a]
private theorem xor3_bca {n} (a b c : BitVec n) : b ^^^ c ^^^ a = a ^^^ b ^^^ c := by
  rw [BitVec.xor_comm (b ^^^ c) a, ← BitVec.xor_assoc a b c]
private theorem xor3_cab {n} (a b c : BitVec n) : c ^^^ a ^^^ b = a ^^^ b ^^^ c := by
  rw [BitVec.xor_comm c a, BitVec.xor_assoc a c b, BitVec.xor_comm c b,
      ← BitVec.xor_assoc a b c]
private theorem xor3_cba {n} (a b c : BitVec n) : c ^^^ b ^^^ a = a ^^^ b ^^^ c := by
  rw [BitVec.xor_comm c b]
  exact xor3_bca a b c

private theorem nodup3_no_attack_Z
    (a b c : Fin 252) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsyn : mech_xstab_syn a ^^^ mech_xstab_syn b ^^^ mech_xstab_syn c = 0)
    (hlx : mech_lx a ^^^ mech_lx b ^^^ mech_lx c ≠ 0) : False := by
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hac' : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have hbc' : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  rcases (show (a.val < b.val ∧ b.val < c.val) ∨ (a.val < c.val ∧ c.val < b.val) ∨
              (b.val < a.val ∧ a.val < c.val) ∨ (b.val < c.val ∧ c.val < a.val) ∨
              (c.val < a.val ∧ a.val < b.val) ∨ (c.val < b.val ∧ b.val < a.val) by omega) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact no_3_chain_attack_sorted_Z a b c h1 h2 ⟨hsyn, hlx⟩
  · exact no_3_chain_attack_sorted_Z a c b h1 h2
      ⟨(xor3_acb _ _ _).symm ▸ hsyn, fun heq => hlx (xor3_acb _ _ _ ▸ heq)⟩
  · exact no_3_chain_attack_sorted_Z b a c h1 h2
      ⟨(xor3_bac _ _ _).symm ▸ hsyn, fun heq => hlx (xor3_bac _ _ _ ▸ heq)⟩
  · exact no_3_chain_attack_sorted_Z b c a h1 h2
      ⟨(xor3_bca _ _ _).symm ▸ hsyn, fun heq => hlx (xor3_bca _ _ _ ▸ heq)⟩
  · exact no_3_chain_attack_sorted_Z c a b h1 h2
      ⟨(xor3_cab _ _ _).symm ▸ hsyn, fun heq => hlx (xor3_cab _ _ _ ▸ heq)⟩
  · exact no_3_chain_attack_sorted_Z c b a h1 h2
      ⟨(xor3_cba _ _ _).symm ▸ hsyn, fun heq => hlx (xor3_cba _ _ _ ▸ heq)⟩

private theorem nodup_length_3 (l : List (Fin 252)) (hlen : l.length = 3) (hnodup : l.Nodup) :
    ∃ (a b c : Fin 252), l = [a, b, c] ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  match l, hlen with
  | [a, b, c], _ =>
    refine ⟨a, b, c, rfl, ?_, ?_, ?_⟩
    · intro hab; rw [hab] at hnodup
      exact (List.nodup_cons.mp hnodup).1 (List.mem_cons_self)
    · intro hac; rw [hac] at hnodup
      exact (List.nodup_cons.mp hnodup).1 (List.mem_cons_of_mem _ List.mem_cons_self)
    · intro hbc; rw [hbc] at hnodup
      exact (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1 List.mem_cons_self

theorem discharge_length_3_Z (chain : List (Fin 252))
    (hchain_syn : chain_xor_syn_Z chain = 0)
    (hchain_lx : chain_xor_lx chain ≠ 0)
    (hreduce_len : (QStab.Paper.BB72BV.reduce chain).length = 3) : False := by
  obtain ⟨a, b, c, hreq, hab, hac, hbc⟩ :=
    nodup_length_3 (QStab.Paper.BB72BV.reduce chain) hreduce_len (QStab.Paper.BB72BV.reduce_nodup chain)
  have hsyn_red : chain_xor_syn_Z (QStab.Paper.BB72BV.reduce chain) = 0 := by
    rw [chain_xor_syn_Z_reduce]; exact hchain_syn
  have hlx_red : chain_xor_lx (QStab.Paper.BB72BV.reduce chain) ≠ 0 := by
    rw [chain_xor_lx_reduce]; exact hchain_lx
  rw [hreq] at hsyn_red hlx_red
  have hsyn3 : mech_xstab_syn a ^^^ mech_xstab_syn b ^^^ mech_xstab_syn c = 0 := by
    have h1 : chain_xor_syn_Z [a, b, c] =
        mech_xstab_syn a ^^^ mech_xstab_syn b ^^^ mech_xstab_syn c := by
      show mech_xstab_syn a ^^^ (mech_xstab_syn b ^^^ (mech_xstab_syn c ^^^ 0)) = _
      simp [BitVec.xor_assoc]
    rw [← h1]; exact hsyn_red
  have hlx3 : mech_lx a ^^^ mech_lx b ^^^ mech_lx c ≠ 0 := by
    have h2 : chain_xor_lx [a, b, c] =
        mech_lx a ^^^ mech_lx b ^^^ mech_lx c := by
      show mech_lx a ^^^ (mech_lx b ^^^ (mech_lx c ^^^ 0)) = _
      simp [BitVec.xor_assoc]
    rw [← h2]; exact hlx_red
  exact nodup3_no_attack_Z a b c hab hac hbc hsyn3 hlx3

/-! ## Length-5 reduced chain discharge via mergeSort -/

private theorem nodup5_strict_sorted (l : List (Fin 252))
    (hlen : l.length = 5) (hnodup : l.Nodup) :
    ∃ (i j k m n : Fin 252),
      l ~ [i, j, k, m, n] ∧
      i.val < j.val ∧ j.val < k.val ∧ k.val < m.val ∧ m.val < n.val := by
  let le : Fin 252 → Fin 252 → Bool := fun a b => a.val ≤ b.val
  let ls := l.mergeSort le
  have hperm : l ~ ls := (List.mergeSort_perm l le).symm
  have hls_nodup : ls.Nodup := hperm.nodup_iff.mp hnodup
  have hls_len : ls.length = 5 := hperm.length_eq ▸ hlen
  have hls_pair : ls.Pairwise (fun a b => le a b = true) := by
    apply List.pairwise_mergeSort
    · intro a b c hab hbc; simp [le] at *; omega
    · intro a b; simp [le]; omega
  match ls, hls_len, hls_nodup, hls_pair with
  | [i, j, k, m, n], _, hnod, hp =>
    refine ⟨i, j, k, m, n, hperm, ?_, ?_, ?_, ?_⟩
    have hnod_pair := List.nodup_iff_pairwise_ne.mp hnod
    all_goals (simp_all [le, List.pairwise_cons]; omega)

theorem discharge_length_5_Z (chain : List (Fin 252))
    (hchain_syn : chain_xor_syn_Z chain = 0)
    (hchain_lx : chain_xor_lx chain ≠ 0)
    (hreduce_len : (QStab.Paper.BB72BV.reduce chain).length = 5) : False := by
  obtain ⟨i, j, k, m, n, hperm, hij, hjk, hkm, hmn⟩ :=
    nodup5_strict_sorted (QStab.Paper.BB72BV.reduce chain) hreduce_len (QStab.Paper.BB72BV.reduce_nodup chain)
  have hsyn_red : chain_xor_syn_Z (QStab.Paper.BB72BV.reduce chain) = 0 := by
    rw [chain_xor_syn_Z_reduce]; exact hchain_syn
  have hlx_red : chain_xor_lx (QStab.Paper.BB72BV.reduce chain) ≠ 0 := by
    rw [chain_xor_lx_reduce]; exact hchain_lx
  rw [chain_xor_syn_Z_perm hperm] at hsyn_red
  rw [chain_xor_lx_perm hperm] at hlx_red
  have hsyn5 : mech_xstab_syn i ^^^ mech_xstab_syn j ^^^ mech_xstab_syn k ^^^
               mech_xstab_syn m ^^^ mech_xstab_syn n = 0 := by
    have h1 : chain_xor_syn_Z [i, j, k, m, n] =
        mech_xstab_syn i ^^^ mech_xstab_syn j ^^^ mech_xstab_syn k ^^^
        mech_xstab_syn m ^^^ mech_xstab_syn n := by
      show mech_xstab_syn i ^^^ (mech_xstab_syn j ^^^ (mech_xstab_syn k ^^^ (mech_xstab_syn m ^^^ (mech_xstab_syn n ^^^ 0)))) = _
      simp [BitVec.xor_assoc]
    rw [← h1]; exact hsyn_red
  have hlx5 : mech_lx i ^^^ mech_lx j ^^^ mech_lx k ^^^
              mech_lx m ^^^ mech_lx n ≠ 0 := by
    have h2 : chain_xor_lx [i, j, k, m, n] =
        mech_lx i ^^^ mech_lx j ^^^ mech_lx k ^^^
        mech_lx m ^^^ mech_lx n := by
      show mech_lx i ^^^ (mech_lx j ^^^ (mech_lx k ^^^ (mech_lx m ^^^ (mech_lx n ^^^ 0)))) = _
      simp [BitVec.xor_assoc]
    rw [← h2]; exact hlx_red
  exact no_5_chain_attack_sorted_Z i j k m n hij hjk hkm hmn ⟨hsyn5, hlx5⟩

/-! ## FINAL THEOREM: bb_chain_attack_Z_k5 -/

theorem bb_chain_attack_Z_k5 :
    ∀ chain : List (Fin 252), chain.length = 5 →
      bb_chain_attack_Z chain = false := by
  intro chain hlen
  by_contra hatt
  rw [Bool.not_eq_false] at hatt
  obtain ⟨hsyn, hlx⟩ := (bb_chain_attack_Z_iff_syn _).mp hatt
  have hred_len_le : (QStab.Paper.BB72BV.reduce chain).length ≤ 5 := by
    have := QStab.Paper.BB72BV.reduce_length_le chain; omega
  have hred_len_par : (QStab.Paper.BB72BV.reduce chain).length % 2 = 1 := by
    have := QStab.Paper.BB72BV.reduce_length_parity chain; omega
  match h : (QStab.Paper.BB72BV.reduce chain).length with
  | 0 => omega
  | 1 => exact discharge_length_1_Z chain hsyn hlx h
  | 2 => omega
  | 3 => exact discharge_length_3_Z chain hsyn hlx h
  | 4 => omega
  | 5 => exact discharge_length_5_Z chain hsyn hlx h
  | n + 6 => omega

/-- **No Z-chain of length ≤ 5 is a successful Z-side attack** (UNCONDITIONAL). -/
theorem bb_chain_attack_Z_le_5 :
    ∀ chain : List (Fin 252), chain.length ≤ 5 →
      bb_chain_attack_Z chain = false := by
  intro chain h
  match hlen : chain.length with
  | 0 => exact bb_chain_attack_Z_k0 chain hlen
  | 1 => exact bb_chain_attack_Z_k1 chain hlen
  | 2 => exact bb_chain_attack_Z_k2 chain hlen
  | 3 => exact bb_chain_attack_Z_k3 chain hlen
  | 4 => exact QStab.Paper.BB72ChainAttackK4Z.bb_chain_attack_Z_k4 chain hlen
  | 5 => exact bb_chain_attack_Z_k5 chain hlen
  | n + 6 => omega

end QStab.Paper.BB72ChainAttackFullZ
