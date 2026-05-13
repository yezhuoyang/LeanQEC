import QStab.Paper.BB72ChainListReduce
import QStab.Paper.BB72SynForallK13
import QStab.Paper.BB72SynForallK5Extract
import QStab.Paper.BB72ChainAttackK4
import QStab.Paper.BB72ChainAttack

/-!
# Full chain attack discharge for arbitrary length-5 chains

Composes:
  * `reduce` infrastructure (cancels duplicates).
  * `chain_xor_syn_perm` / `chain_xor_lz_perm` (sort via permutation).
  * `no_1_chain_attack`, `no_3_chain_attack_sorted` (small K cases).
  * Hypothesis `h5_sorted` for K=5 sorted distinct (pending the
    K=5 List.any build; once `BB72SynForallK5` lands, becomes
    unconditional via `List.any_eq_false_iff_forall_not`).

For length-5 chains:
  - bb_chain_attack chain ↔ chain_xor_syn = 0 ∧ chain_xor_lz ≠ 0.
  - reduce chain: same XOR, Nodup, length ∈ {1, 3, 5}.
  - For each length case, sort and apply corresponding K-forall.
-/

open List

namespace QStab.Paper.BB72ChainAttackFull

open QStab.Paper.BB72BV
open QStab.Paper.BB72ChainAttack

/-- Helper: a Nodup list of length 1 is `[a]` for some `a`. -/
private theorem nodup_length_1 (l : List (Fin 252)) (h : l.length = 1) :
    ∃ a, l = [a] := by
  match l, h with
  | [a], _ => exact ⟨a, rfl⟩

/-! ## Discharge length-1 reduced chain -/

/-- If `(reduce chain).length = 1` and the chain has the attack property,
    we get a contradiction via `no_1_chain_attack`. -/
theorem discharge_length_1 (chain : List (Fin 252))
    (hchain_syn : chain_xor_syn chain = 0)
    (hchain_lz : chain_xor_lz chain ≠ 0)
    (hreduce_len : (reduce chain).length = 1) : False := by
  obtain ⟨a, ha⟩ := nodup_length_1 (reduce chain) hreduce_len
  have hsyn_red : chain_xor_syn (reduce chain) = 0 := by
    rw [chain_xor_syn_reduce]; exact hchain_syn
  rw [ha] at hsyn_red
  -- chain_xor_syn [a] = mech_syn a ^^^ 0 = mech_syn a
  have h1 : chain_xor_syn [a] = mech_syn a := by
    show mech_syn a ^^^ 0 = mech_syn a
    exact BitVec.xor_zero
  rw [h1] at hsyn_red
  have hlz_red : chain_xor_lz (reduce chain) ≠ 0 := by
    rw [chain_xor_lz_reduce]; exact hchain_lz
  rw [ha] at hlz_red
  have h2 : chain_xor_lz [a] = mech_lz a := by
    show mech_lz a ^^^ 0 = mech_lz a
    exact BitVec.xor_zero
  rw [h2] at hlz_red
  exact no_1_chain_attack a ⟨hsyn_red, hlz_red⟩

/-! ## Discharge length-3 reduced chain (Nodup, sorted via permutation) -/

/-- XOR rearrangement helpers: 3-element permutations. -/
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

/-- For 3 distinct `Fin 252` elements (any order), no attack. -/
private theorem nodup3_no_attack
    (a b c : Fin 252) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsyn : mech_syn a ^^^ mech_syn b ^^^ mech_syn c = 0)
    (hlz : mech_lz a ^^^ mech_lz b ^^^ mech_lz c ≠ 0) : False := by
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hac' : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have hbc' : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  rcases (show (a.val < b.val ∧ b.val < c.val) ∨ (a.val < c.val ∧ c.val < b.val) ∨
              (b.val < a.val ∧ a.val < c.val) ∨ (b.val < c.val ∧ c.val < a.val) ∨
              (c.val < a.val ∧ a.val < b.val) ∨ (c.val < b.val ∧ b.val < a.val) by omega) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact no_3_chain_attack_sorted a b c h1 h2 ⟨hsyn, hlz⟩
  · exact no_3_chain_attack_sorted a c b h1 h2
      ⟨(xor3_acb _ _ _).symm ▸ hsyn, fun heq => hlz (xor3_acb _ _ _ ▸ heq)⟩
  · exact no_3_chain_attack_sorted b a c h1 h2
      ⟨(xor3_bac _ _ _).symm ▸ hsyn, fun heq => hlz (xor3_bac _ _ _ ▸ heq)⟩
  · exact no_3_chain_attack_sorted b c a h1 h2
      ⟨(xor3_bca _ _ _).symm ▸ hsyn, fun heq => hlz (xor3_bca _ _ _ ▸ heq)⟩
  · exact no_3_chain_attack_sorted c a b h1 h2
      ⟨(xor3_cab _ _ _).symm ▸ hsyn, fun heq => hlz (xor3_cab _ _ _ ▸ heq)⟩
  · exact no_3_chain_attack_sorted c b a h1 h2
      ⟨(xor3_cba _ _ _).symm ▸ hsyn, fun heq => hlz (xor3_cba _ _ _ ▸ heq)⟩

/-- Helper: a Nodup list of length 3 is `[a, b, c]` with all distinct. -/
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

/-- Discharge length-3 reduced chain via `nodup3_no_attack`. -/
theorem discharge_length_3 (chain : List (Fin 252))
    (hchain_syn : chain_xor_syn chain = 0)
    (hchain_lz : chain_xor_lz chain ≠ 0)
    (hreduce_len : (reduce chain).length = 3) : False := by
  obtain ⟨a, b, c, hreq, hab, hac, hbc⟩ := nodup_length_3 (reduce chain) hreduce_len (reduce_nodup chain)
  have hsyn_red : chain_xor_syn (reduce chain) = 0 := by rw [chain_xor_syn_reduce]; exact hchain_syn
  have hlz_red : chain_xor_lz (reduce chain) ≠ 0 := by rw [chain_xor_lz_reduce]; exact hchain_lz
  rw [hreq] at hsyn_red hlz_red
  -- chain_xor_syn [a, b, c] = mech_syn a ^^^ mech_syn b ^^^ mech_syn c
  have hsyn3 : mech_syn a ^^^ mech_syn b ^^^ mech_syn c = 0 := by
    have h1 : chain_xor_syn [a, b, c] = mech_syn a ^^^ mech_syn b ^^^ mech_syn c := by
      show mech_syn a ^^^ (mech_syn b ^^^ (mech_syn c ^^^ 0)) = _
      simp [BitVec.xor_assoc]
    rw [← h1]; exact hsyn_red
  have hlz3 : mech_lz a ^^^ mech_lz b ^^^ mech_lz c ≠ 0 := by
    have h2 : chain_xor_lz [a, b, c] = mech_lz a ^^^ mech_lz b ^^^ mech_lz c := by
      show mech_lz a ^^^ (mech_lz b ^^^ (mech_lz c ^^^ 0)) = _
      simp [BitVec.xor_assoc]
    rw [← h2]; exact hlz_red
  exact nodup3_no_attack a b c hab hac hbc hsyn3 hlz3

/-! ## Length-5 discharge via mergeSort + Nodup → strict -/

/-- Helper: For Nodup list of length 5, mergeSort gives strictly sorted [i,j,k,l,m]. -/
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
    -- Extract Nodup ⇒ ≠ pairwise.
    have hnod_pair := List.nodup_iff_pairwise_ne.mp hnod
    -- Adjacent pairs from Pairwise (le): (i,j), (j,k), (k,m), (m,n).
    -- Combined with ≠ from nodup, get strict <.
    all_goals (simp_all [le, List.pairwise_cons]; omega)

/-- Discharge length-5 reduced chain via `no_5_chain_attack_sorted`. -/
theorem discharge_length_5 (chain : List (Fin 252))
    (hchain_syn : chain_xor_syn chain = 0)
    (hchain_lz : chain_xor_lz chain ≠ 0)
    (hreduce_len : (reduce chain).length = 5) : False := by
  obtain ⟨i, j, k, m, n, hperm, hij, hjk, hkm, hmn⟩ :=
    nodup5_strict_sorted (reduce chain) hreduce_len (reduce_nodup chain)
  -- chain_xor_syn (reduce chain) = chain_xor_syn [i,j,k,m,n] by perm
  have hsyn_red : chain_xor_syn (reduce chain) = 0 := by rw [chain_xor_syn_reduce]; exact hchain_syn
  have hlz_red : chain_xor_lz (reduce chain) ≠ 0 := by rw [chain_xor_lz_reduce]; exact hchain_lz
  rw [chain_xor_syn_perm hperm] at hsyn_red
  rw [chain_xor_lz_perm hperm] at hlz_red
  have hsyn5 : mech_syn i ^^^ mech_syn j ^^^ mech_syn k ^^^ mech_syn m ^^^ mech_syn n = 0 := by
    have h1 : chain_xor_syn [i, j, k, m, n] =
        mech_syn i ^^^ mech_syn j ^^^ mech_syn k ^^^ mech_syn m ^^^ mech_syn n := by
      show mech_syn i ^^^ (mech_syn j ^^^ (mech_syn k ^^^ (mech_syn m ^^^ (mech_syn n ^^^ 0)))) = _
      simp [BitVec.xor_assoc]
    rw [← h1]; exact hsyn_red
  have hlz5 : mech_lz i ^^^ mech_lz j ^^^ mech_lz k ^^^ mech_lz m ^^^ mech_lz n ≠ 0 := by
    have h2 : chain_xor_lz [i, j, k, m, n] =
        mech_lz i ^^^ mech_lz j ^^^ mech_lz k ^^^ mech_lz m ^^^ mech_lz n := by
      show mech_lz i ^^^ (mech_lz j ^^^ (mech_lz k ^^^ (mech_lz m ^^^ (mech_lz n ^^^ 0)))) = _
      simp [BitVec.xor_assoc]
    rw [← h2]; exact hlz_red
  exact no_5_chain_attack_sorted i j k m n hij hjk hkm hmn ⟨hsyn5, hlz5⟩

/-! ## FINAL THEOREM: bb_chain_attack_k5 -/

/-- **No 5-element chain is a successful X-side attack** (any order, any duplicates).
    Composes:
      * `bb_chain_attack_iff_syn` (the structural bridge).
      * `reduce` (cancel duplicates → Nodup).
      * `discharge_length_{1, 3, 5}` (cases of reduced length, all parity-odd).
-/
theorem bb_chain_attack_k5 :
    ∀ chain : List (Fin 252), chain.length = 5 →
      bb_chain_attack chain = false := by
  intro chain hlen
  by_contra hatt
  rw [Bool.not_eq_false] at hatt
  obtain ⟨hsyn, hlz⟩ := (bb_chain_attack_iff_syn _).mp hatt
  -- chain_xor_syn chain = 0, chain_xor_lz chain ≠ 0
  have hred_len_le : (reduce chain).length ≤ 5 := by
    have := reduce_length_le chain; omega
  have hred_len_par : (reduce chain).length % 2 = 1 := by
    have := reduce_length_parity chain; omega
  -- (reduce chain).length ∈ {1, 3, 5}
  match h : (reduce chain).length with
  | 0 => omega
  | 1 => exact discharge_length_1 chain hsyn hlz h
  | 2 => omega
  | 3 => exact discharge_length_3 chain hsyn hlz h
  | 4 => omega
  | 5 => exact discharge_length_5 chain hsyn hlz h
  | n + 6 => omega

/-- **No chain of length ≤ 5 is a successful X-side attack** (UNCONDITIONAL).
    The composite of all K=0..5 cases, all proven zero-sorry. -/
theorem bb_chain_attack_le_5 :
    ∀ chain : List (Fin 252), chain.length ≤ 5 →
      bb_chain_attack chain = false := by
  intro chain h
  match hlen : chain.length with
  | 0 => exact bb_chain_attack_k0 chain hlen
  | 1 => exact bb_chain_attack_k1 chain hlen
  | 2 => exact bb_chain_attack_k2 chain hlen
  | 3 => exact bb_chain_attack_k3 chain hlen
  | 4 => exact QStab.Paper.BB72ChainAttackK4.bb_chain_attack_k4 chain hlen
  | 5 => exact bb_chain_attack_k5 chain hlen
  | n + 6 => omega

end QStab.Paper.BB72ChainAttackFull
