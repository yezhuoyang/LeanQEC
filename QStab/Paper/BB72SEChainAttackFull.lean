import QStab.Paper.BB72SEChainListReduce
import QStab.Paper.BB72SESynForall
import QStab.Paper.BB72SESynForallK5Extract
import QStab.Paper.BB72SEChainAttackK4

open List

namespace QStab.Paper.BB72SEChainAttackFull

open QStab.Paper.BB72BVSE
open QStab.Paper.BB72ReachableEBridgeSE

private theorem nodup_length_1 (l : List (Fin 252)) (h : l.length = 1) :
    ∃ a, l = [a] := by
  match l, h with
  | [a], _ => exact ⟨a, rfl⟩

theorem discharge_length_1_SE (chain : List (Fin 252))
    (hchain_syn : chain_xor_se_syn chain = 0)
    (hchain_lz : chain_xor_se_lz chain ≠ 0)
    (hreduce_len : (QStab.Paper.BB72BV.reduce chain).length = 1) : False := by
  obtain ⟨a, ha⟩ := nodup_length_1 (QStab.Paper.BB72BV.reduce chain) hreduce_len
  have hsyn_red : chain_xor_se_syn (QStab.Paper.BB72BV.reduce chain) = 0 := by
    rw [chain_xor_se_syn_reduce]; exact hchain_syn
  rw [ha] at hsyn_red
  have h1 : chain_xor_se_syn [a] = mech_se_syn a := by
    show mech_se_syn a ^^^ 0 = mech_se_syn a
    exact BitVec.xor_zero
  rw [h1] at hsyn_red
  have hlz_red : chain_xor_se_lz (QStab.Paper.BB72BV.reduce chain) ≠ 0 := by
    rw [chain_xor_se_lz_reduce]; exact hchain_lz
  rw [ha] at hlz_red
  have h2 : chain_xor_se_lz [a] = mech_se_lz a := by
    show mech_se_lz a ^^^ 0 = mech_se_lz a
    exact BitVec.xor_zero
  rw [h2] at hlz_red
  exact no_1_chain_attack_SE a ⟨hsyn_red, hlz_red⟩

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

private theorem nodup3_no_attack_SE
    (a b c : Fin 252) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsyn : mech_se_syn a ^^^ mech_se_syn b ^^^ mech_se_syn c = 0)
    (hlz : mech_se_lz a ^^^ mech_se_lz b ^^^ mech_se_lz c ≠ 0) : False := by
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hac' : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have hbc' : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  rcases (show (a.val < b.val ∧ b.val < c.val) ∨ (a.val < c.val ∧ c.val < b.val) ∨
              (b.val < a.val ∧ a.val < c.val) ∨ (b.val < c.val ∧ c.val < a.val) ∨
              (c.val < a.val ∧ a.val < b.val) ∨ (c.val < b.val ∧ b.val < a.val) by omega) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact no_3_chain_attack_sorted_SE a b c h1 h2 ⟨hsyn, hlz⟩
  · exact no_3_chain_attack_sorted_SE a c b h1 h2
      ⟨(xor3_acb _ _ _).symm ▸ hsyn, fun heq => hlz (xor3_acb _ _ _ ▸ heq)⟩
  · exact no_3_chain_attack_sorted_SE b a c h1 h2
      ⟨(xor3_bac _ _ _).symm ▸ hsyn, fun heq => hlz (xor3_bac _ _ _ ▸ heq)⟩
  · exact no_3_chain_attack_sorted_SE b c a h1 h2
      ⟨(xor3_bca _ _ _).symm ▸ hsyn, fun heq => hlz (xor3_bca _ _ _ ▸ heq)⟩
  · exact no_3_chain_attack_sorted_SE c a b h1 h2
      ⟨(xor3_cab _ _ _).symm ▸ hsyn, fun heq => hlz (xor3_cab _ _ _ ▸ heq)⟩
  · exact no_3_chain_attack_sorted_SE c b a h1 h2
      ⟨(xor3_cba _ _ _).symm ▸ hsyn, fun heq => hlz (xor3_cba _ _ _ ▸ heq)⟩

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

theorem discharge_length_3_SE (chain : List (Fin 252))
    (hchain_syn : chain_xor_se_syn chain = 0)
    (hchain_lz : chain_xor_se_lz chain ≠ 0)
    (hreduce_len : (QStab.Paper.BB72BV.reduce chain).length = 3) : False := by
  obtain ⟨a, b, c, hreq, hab, hac, hbc⟩ :=
    nodup_length_3 (QStab.Paper.BB72BV.reduce chain) hreduce_len (QStab.Paper.BB72BV.reduce_nodup chain)
  have hsyn_red : chain_xor_se_syn (QStab.Paper.BB72BV.reduce chain) = 0 := by
    rw [chain_xor_se_syn_reduce]; exact hchain_syn
  have hlz_red : chain_xor_se_lz (QStab.Paper.BB72BV.reduce chain) ≠ 0 := by
    rw [chain_xor_se_lz_reduce]; exact hchain_lz
  rw [hreq] at hsyn_red hlz_red
  have hsyn3 : mech_se_syn a ^^^ mech_se_syn b ^^^ mech_se_syn c = 0 := by
    have h1 : chain_xor_se_syn [a, b, c] =
        mech_se_syn a ^^^ mech_se_syn b ^^^ mech_se_syn c := by
      show mech_se_syn a ^^^ (mech_se_syn b ^^^ (mech_se_syn c ^^^ 0)) = _
      simp [BitVec.xor_assoc]
    rw [← h1]; exact hsyn_red
  have hlz3 : mech_se_lz a ^^^ mech_se_lz b ^^^ mech_se_lz c ≠ 0 := by
    have h2 : chain_xor_se_lz [a, b, c] =
        mech_se_lz a ^^^ mech_se_lz b ^^^ mech_se_lz c := by
      show mech_se_lz a ^^^ (mech_se_lz b ^^^ (mech_se_lz c ^^^ 0)) = _
      simp [BitVec.xor_assoc]
    rw [← h2]; exact hlz_red
  exact nodup3_no_attack_SE a b c hab hac hbc hsyn3 hlz3

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

theorem discharge_length_5_SE (chain : List (Fin 252))
    (hchain_syn : chain_xor_se_syn chain = 0)
    (hchain_lz : chain_xor_se_lz chain ≠ 0)
    (hreduce_len : (QStab.Paper.BB72BV.reduce chain).length = 5) : False := by
  obtain ⟨i, j, k, m, n, hperm, hij, hjk, hkm, hmn⟩ :=
    nodup5_strict_sorted (QStab.Paper.BB72BV.reduce chain) hreduce_len (QStab.Paper.BB72BV.reduce_nodup chain)
  have hsyn_red : chain_xor_se_syn (QStab.Paper.BB72BV.reduce chain) = 0 := by
    rw [chain_xor_se_syn_reduce]; exact hchain_syn
  have hlz_red : chain_xor_se_lz (QStab.Paper.BB72BV.reduce chain) ≠ 0 := by
    rw [chain_xor_se_lz_reduce]; exact hchain_lz
  rw [chain_xor_se_syn_perm hperm] at hsyn_red
  rw [chain_xor_se_lz_perm hperm] at hlz_red
  have hsyn5 : mech_se_syn i ^^^ mech_se_syn j ^^^ mech_se_syn k ^^^
               mech_se_syn m ^^^ mech_se_syn n = 0 := by
    have h1 : chain_xor_se_syn [i, j, k, m, n] =
        mech_se_syn i ^^^ mech_se_syn j ^^^ mech_se_syn k ^^^
        mech_se_syn m ^^^ mech_se_syn n := by
      show mech_se_syn i ^^^ (mech_se_syn j ^^^ (mech_se_syn k ^^^ (mech_se_syn m ^^^ (mech_se_syn n ^^^ 0)))) = _
      simp [BitVec.xor_assoc]
    rw [← h1]; exact hsyn_red
  have hlz5 : mech_se_lz i ^^^ mech_se_lz j ^^^ mech_se_lz k ^^^
              mech_se_lz m ^^^ mech_se_lz n ≠ 0 := by
    have h2 : chain_xor_se_lz [i, j, k, m, n] =
        mech_se_lz i ^^^ mech_se_lz j ^^^ mech_se_lz k ^^^
        mech_se_lz m ^^^ mech_se_lz n := by
      show mech_se_lz i ^^^ (mech_se_lz j ^^^ (mech_se_lz k ^^^ (mech_se_lz m ^^^ (mech_se_lz n ^^^ 0)))) = _
      simp [BitVec.xor_assoc]
    rw [← h2]; exact hlz_red
  exact no_5_chain_attack_sorted_SE i j k m n hij hjk hkm hmn ⟨hsyn5, hlz5⟩

theorem bb_chain_attack_SE_k5 :
    ∀ chain : List (Fin 252), chain.length = 5 →
      bb_chain_attack_SE chain = false := by
  intro chain hlen
  by_contra hatt
  rw [Bool.not_eq_false] at hatt
  obtain ⟨hsyn, hlz⟩ := (bb_chain_attack_SE_iff_syn _).mp hatt
  have hred_len_le : (QStab.Paper.BB72BV.reduce chain).length ≤ 5 := by
    have := QStab.Paper.BB72BV.reduce_length_le chain; omega
  have hred_len_par : (QStab.Paper.BB72BV.reduce chain).length % 2 = 1 := by
    have := QStab.Paper.BB72BV.reduce_length_parity chain; omega
  match h : (QStab.Paper.BB72BV.reduce chain).length with
  | 0 => omega
  | 1 => exact discharge_length_1_SE chain hsyn hlz h
  | 2 => omega
  | 3 => exact discharge_length_3_SE chain hsyn hlz h
  | 4 => omega
  | 5 => exact discharge_length_5_SE chain hsyn hlz h
  | n + 6 => omega

theorem bb_chain_attack_SE_le_5 :
    ∀ chain : List (Fin 252), chain.length ≤ 5 →
      bb_chain_attack_SE chain = false := by
  intro chain h
  match hlen : chain.length with
  | 0 => exact bb_chain_attack_SE_k0 chain hlen
  | 1 => exact bb_chain_attack_SE_k1 chain hlen
  | 2 => exact bb_chain_attack_SE_k2 chain hlen
  | 3 => exact bb_chain_attack_SE_k3 chain hlen
  | 4 => exact QStab.Paper.BB72SEChainAttackK4.bb_chain_attack_SE_k4 chain hlen
  | 5 => exact bb_chain_attack_SE_k5 chain hlen
  | n + 6 => omega

end QStab.Paper.BB72SEChainAttackFull
