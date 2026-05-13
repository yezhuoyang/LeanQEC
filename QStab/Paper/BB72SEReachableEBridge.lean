import QStab.Paper.BB72ReachableEBridge
import QStab.Paper.BB72SEInstance

/-!
# `reachableE` → chain-XOR reduction (SE-side)

Mirror of `BB72ReachableEBridge` for the SE scheduling. Reuses:
  * `xContent` (X-only projection) — same as NZ X-side.
  * `parity_zstab_eq_xContent`, `parity_lx_eq_xContent` — already proven.
  * `parity_X_only_X_only` — already proven.

New: `bb_se_xMech` enumeration + analogous reachableE → chain XOR existence.
-/

namespace QStab.Paper.BB72ReachableEBridgeSE

open QStab QStab.Paper.BB72Instance QStab.Paper.BB72SEInstance ErrorVec
open QStab.Paper.BB72ReachableEBridge

/-- bb_se_allHooks has length 180. -/
theorem bb_se_allHooks_length : bb_se_allHooks.length = 180 := by native_decide

/-- Each SE X-mech is X-only. -/
theorem bb_se_xMech_is_X_only :
    ∀ i : Fin 252, QStab.Paper.BB72BVBridge.is_X_only (bb_se_xMech i) = true := by
  native_decide

/-- xContent fixes the 252 SE X-mechs. -/
theorem xContent_seMech (i : Fin 252) :
    xContent (bb_se_xMech i) = bb_se_xMech i :=
  xContent_fixes_X_only _ (bb_se_xMech_is_X_only i)

/-- Type-0 SE X-mech at qubit `i` (i : Fin 72) equals the singleton X-update of identity. -/
theorem bb_se_xMech_type0 (i : Fin 72) :
    bb_se_xMech ⟨i.val, by omega⟩ =
      ErrorVec.update (ErrorVec.identity 72) i .X := by
  unfold bb_se_xMech
  simp [i.isLt]

/-- Any hook in bb_se_allHooks corresponds to an SE X-mech index ≥ 72. -/
theorem bb_se_xMech_hook (h : ErrorVec 72) (hh : h ∈ bb_se_allHooks) :
    ∃ j : Fin 252, bb_se_xMech j = h := by
  obtain ⟨n, hn_lt, hn_get⟩ := List.getElem_of_mem hh
  rw [bb_se_allHooks_length] at hn_lt
  refine ⟨⟨72 + n, by omega⟩, ?_⟩
  unfold bb_se_xMech
  have hge : ¬ (72 + n < 72) := by omega
  simp only [hge, ↓reduceDIte]
  have hidx : 72 + n - 72 = n := by omega
  rw [hidx, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by rw [bb_se_allHooks_length]; exact hn_lt)]
  exact hn_get

/-! ## Z-side chain XOR for SE mechs -/

def chain_xor_SE : List (Fin 252) → ErrorVec 72
  | []        => ErrorVec.identity 72
  | i :: rest => ErrorVec.mul (bb_se_xMech i) (chain_xor_SE rest)

/-! ## Inductive existence: xContent of reachableE element is SE chain XOR -/

open QStab.Paper.GenericReachableBridge in
theorem reachableE_xContent_chain_SE :
    ∀ (k : Nat) (E : ErrorVec 72),
      E ∈ reachableE bb_se_allHooks k →
      ∃ chain : List (Fin 252),
        chain.length ≤ k ∧
        chain_xor_SE chain = xContent E := by
  intro k
  induction k with
  | zero =>
    intro E hE
    simp [reachableE] at hE
    refine ⟨[], by simp, ?_⟩
    rw [hE, xContent_identity]
    rfl
  | succ k ih =>
    intro E hE
    simp only [reachableE, List.mem_append] at hE
    rcases hE with (hE_prev | hE_t01) | hE_t2
    · obtain ⟨chain, hlen, hxor⟩ := ih E hE_prev
      exact ⟨chain, by omega, hxor⟩
    · simp only [List.mem_flatMap, List.mem_map] at hE_t01
      obtain ⟨i, _hi_mem, p, hp_mem, e, he_prev, heq⟩ := hE_t01
      obtain ⟨chain', hlen, hxor⟩ := ih e he_prev
      subst heq
      simp [List.mem_cons] at hp_mem
      rcases hp_mem with hpX | hpY | hpZ
      · subst hpX
        refine ⟨⟨i.val, by omega⟩ :: chain', by simp; omega, ?_⟩
        show chain_xor_SE (⟨i.val, _⟩ :: chain') = xContent (ErrorVec.update e i .X)
        unfold chain_xor_SE
        rw [bb_se_xMech_type0, xContent_update]
        unfold xContent_pauli
        rw [hxor]
      · subst hpY
        refine ⟨⟨i.val, by omega⟩ :: chain', by simp; omega, ?_⟩
        show chain_xor_SE (⟨i.val, _⟩ :: chain') = xContent (ErrorVec.update e i .Y)
        unfold chain_xor_SE
        rw [bb_se_xMech_type0, xContent_update]
        unfold xContent_pauli
        rw [hxor]
      · subst hpZ
        refine ⟨chain', by omega, ?_⟩
        rw [xContent_update]
        unfold xContent_pauli
        rw [update_I_eq, identity_mul, hxor]
    · simp only [List.mem_flatMap, List.mem_map] at hE_t2
      obtain ⟨h, hh_mem, e, he_prev, heq⟩ := hE_t2
      obtain ⟨chain', hlen, hxor⟩ := ih e he_prev
      obtain ⟨j, hj_eq⟩ := bb_se_xMech_hook h hh_mem
      subst heq
      refine ⟨j :: chain', by simp; omega, ?_⟩
      unfold chain_xor_SE
      rw [hj_eq, xContent_mul]
      have hh_X_only : QStab.Paper.BB72BVBridge.is_X_only h = true := by
        rw [← hj_eq]; exact bb_se_xMech_is_X_only j
      rw [xContent_fixes_X_only h hh_X_only, hxor]

end QStab.Paper.BB72ReachableEBridgeSE
