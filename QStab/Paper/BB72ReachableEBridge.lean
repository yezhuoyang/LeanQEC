import QStab.Paper.BB72ChainAttackFull
import QStab.Paper.GenericReachableBridge

/-!
# `reachableE` → chain-XOR reduction (X-side)

The chain-attack predicate `bb_chain_attack_le_5` says no chain XOR of ≤ 5
X-mechs is a successful X-side attack. To discharge `bb_NZ_no_X_attack_below_6`,
we need: for any `E ∈ reachableE bb_allHooks 5`, `bb_isSuccess E = false`.

## Structural reduction

For `E : ErrorVec 72`, define `xContent E : ErrorVec 72` as the X-only projection:
  E[i] = .X or .Y → .X
  E[i] = .I or .Z → .I

**Key properties** (proved here):

1. `parity (Z-stab) E = parity (Z-stab) (xContent E)` (Z-stab is Z-only;
   anticommutes with E[i] iff E[i] ∈ {X, Y} = same as for xContent E).
2. Same for L_Z basis vectors.
3. `xContent (E ∈ reachableE bb_allHooks k)` is chain XOR of ≤ k X-mechs
   (single-qubit X/Y updates contribute Type-0 mechs; hook mul contributes
   X-hook mechs; Z updates contribute nothing to X-content).

Combined: `bb_isSuccess E = false` follows from `bb_chain_attack_le_5`.

This iteration: the foundational `xContent` definition and parity equivalence
for Z-only stabs.
-/

namespace QStab.Paper.BB72ReachableEBridge

open QStab QStab.Paper.BB72Instance ErrorVec

/-- Per-Pauli X-content projection. -/
def xContent_pauli : Pauli → Pauli
  | .X => .X
  | .Y => .X
  | .I => .I
  | .Z => .I

/-- X-only projection: maps `.X` and `.Y` to `.X`; `.I` and `.Z` to `.I`. -/
def xContent (E : ErrorVec 72) : ErrorVec 72 := fun i => xContent_pauli (E i)

/-- xContent_pauli is a Pauli-mul homomorphism (Klein-four group quotient onto {I, X}). -/
theorem xContent_pauli_mul (p q : Pauli) :
    xContent_pauli (Pauli.mul p q) =
      Pauli.mul (xContent_pauli p) (xContent_pauli q) := by
  cases p <;> cases q <;> rfl

/-- xContent is an ErrorVec.mul homomorphism. -/
theorem xContent_mul (a b : ErrorVec 72) :
    xContent (ErrorVec.mul a b) = ErrorVec.mul (xContent a) (xContent b) := by
  unfold xContent ErrorVec.mul
  funext i
  exact xContent_pauli_mul (a i) (b i)

/-- xContent fixes the identity. -/
theorem xContent_identity :
    xContent (ErrorVec.identity 72) = ErrorVec.identity 72 := by
  unfold xContent ErrorVec.identity xContent_pauli
  funext i
  rfl

/-- xContent is X-only. -/
theorem xContent_is_X_only (E : ErrorVec 72) :
    QStab.Paper.BB72BVBridge.is_X_only (xContent E) = true := by
  rw [QStab.Paper.BB72BVBridge.is_X_only_iff]
  intro i
  unfold xContent xContent_pauli
  cases E i <;> simp

/-- xContent fixes X-only ErrorVecs. -/
theorem xContent_fixes_X_only (E : ErrorVec 72)
    (h : QStab.Paper.BB72BVBridge.is_X_only E = true) :
    xContent E = E := by
  rw [QStab.Paper.BB72BVBridge.is_X_only_iff] at h
  funext i
  rcases h i with hI | hX
  · unfold xContent xContent_pauli; rw [hI]
  · unfold xContent xContent_pauli; rw [hX]

/-- xContent fixes the 252 X-mechs. -/
theorem xContent_xMech (i : Fin 252) :
    xContent (QStab.Paper.BB72ChainCheck.bb_xMech i) =
      QStab.Paper.BB72ChainCheck.bb_xMech i :=
  xContent_fixes_X_only _ (QStab.Paper.BB72BVBridge.bb_xMech_is_X_only i)

/-- Update by `Pauli.I` is a no-op. -/
theorem update_I_eq (e : ErrorVec 72) (i : Fin 72) :
    ErrorVec.update e i .I = e := by
  unfold ErrorVec.update
  funext j
  by_cases hji : j = i
  · subst hji; simp [Pauli.mul]
  · simp [Function.update_of_ne hji]

/-- Identity is a left identity for ErrorVec.mul. -/
theorem identity_mul (e : ErrorVec 72) :
    ErrorVec.mul (ErrorVec.identity 72) e = e := by
  unfold ErrorVec.mul ErrorVec.identity
  funext j
  rfl

/-- Multiplication by `Pauli.I` on the right. -/
theorem Pauli_mul_I_right (p : Pauli) : Pauli.mul p .I = p := by
  cases p <;> rfl

/-- Update equals left-multiplication by a singleton. -/
theorem update_eq_mul_singleton (e : ErrorVec 72) (i : Fin 72) (p : Pauli) :
    ErrorVec.update e i p =
      ErrorVec.mul (ErrorVec.update (ErrorVec.identity 72) i p) e := by
  unfold ErrorVec.update ErrorVec.mul ErrorVec.identity
  funext j
  by_cases hji : j = i
  · subst hji; simp [Pauli_mul_I_right]
  · simp [Function.update_of_ne hji, Pauli.mul]

/-- xContent of a singleton update at the identity. -/
theorem xContent_singleton (i : Fin 72) (p : Pauli) :
    xContent (ErrorVec.update (ErrorVec.identity 72) i p) =
      ErrorVec.update (ErrorVec.identity 72) i (xContent_pauli p) := by
  unfold xContent ErrorVec.update ErrorVec.identity
  funext j
  by_cases hji : j = i
  · subst hji
    simp [Pauli_mul_I_right]
  · simp [Function.update_of_ne hji]; rfl

/-- xContent under update: factor out as mul (singleton xContent_pauli p) (xContent e). -/
theorem xContent_update (e : ErrorVec 72) (i : Fin 72) (p : Pauli) :
    xContent (ErrorVec.update e i p) =
      ErrorVec.mul
        (ErrorVec.update (ErrorVec.identity 72) i (xContent_pauli p))
        (xContent e) := by
  rw [update_eq_mul_singleton, xContent_mul, xContent_singleton]

/-- Type-0 X-mech at qubit `i` (i : Fin 72) equals the singleton X-update of identity. -/
theorem bb_xMech_type0 (i : Fin 72) :
    QStab.Paper.BB72ChainCheck.bb_xMech ⟨i.val, by omega⟩ =
      ErrorVec.update (ErrorVec.identity 72) i .X := by
  unfold QStab.Paper.BB72ChainCheck.bb_xMech
  simp [i.isLt]

/-- bb_allHooks has length 180. -/
theorem bb_allHooks_length : bb_allHooks.length = 180 := by native_decide

/-- Any hook in bb_allHooks corresponds to an X-mech index ≥ 72. -/
theorem bb_xMech_hook (h : ErrorVec 72) (hh : h ∈ bb_allHooks) :
    ∃ j : Fin 252, QStab.Paper.BB72ChainCheck.bb_xMech j = h := by
  obtain ⟨n, hn_lt, hn_get⟩ := List.getElem_of_mem hh
  rw [bb_allHooks_length] at hn_lt
  refine ⟨⟨72 + n, by omega⟩, ?_⟩
  unfold QStab.Paper.BB72ChainCheck.bb_xMech
  have hge : ¬ (72 + n < 72) := by omega
  simp only [hge, ↓reduceDIte]
  have hidx : 72 + n - 72 = n := by omega
  rw [hidx, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by rw [bb_allHooks_length]; exact hn_lt)]
  exact hn_get

/-- For Z-only stab `z` and any `E`, parity vs E equals parity vs xContent E. -/
theorem parity_z_only_eq_xContent (z E : ErrorVec 72)
    (hz : QStab.Paper.BB72BVBridge.is_Z_only z = true) :
    ErrorVec.parity z E = ErrorVec.parity z (xContent E) := by
  unfold ErrorVec.parity
  have hf : (Finset.univ.filter fun i : Fin 72 =>
                Pauli.anticommutes (z i) (E i) = true)
          = Finset.univ.filter fun i : Fin 72 =>
                Pauli.anticommutes (z i) (xContent E i) = true := by
    apply Finset.filter_congr
    intro i _
    rw [QStab.Paper.BB72BVBridge.is_Z_only_iff] at hz
    rcases hz i with hzI | hzZ
    · rw [hzI]; simp [Pauli.anticommutes]
    · rw [hzZ]
      unfold xContent xContent_pauli
      generalize E i = e
      cases e <;> simp [Pauli.anticommutes]
  rw [hf]

/-- Specialization: for any Z-stab from BB72, parity of E equals parity of xContent E. -/
theorem parity_zstab_eq_xContent (s : Fin 36) (E : ErrorVec 72) :
    ErrorVec.parity (bb_stabilizers (QStab.Paper.BB72BVBridge.zStabIdx s)) E =
      ErrorVec.parity (bb_stabilizers (QStab.Paper.BB72BVBridge.zStabIdx s)) (xContent E) :=
  parity_z_only_eq_xContent _ _ (QStab.Paper.BB72BVBridge.is_Z_only_bb_zstab s)

/-- Specialization: for any L_Z basis vector, parity of E equals parity of xContent E. -/
theorem parity_lz_eq_xContent (l : Fin 12) (E : ErrorVec 72) :
    ErrorVec.parity (bb_logicalZ_basis l) E =
      ErrorVec.parity (bb_logicalZ_basis l) (xContent E) :=
  parity_z_only_eq_xContent _ _ (QStab.Paper.BB72BVBridge.is_Z_only_bb_lz l)

/-! ## X-only × X-only parity is zero -/

theorem parity_X_only_X_only (a b : ErrorVec 72)
    (ha : QStab.Paper.BB72BVBridge.is_X_only a = true)
    (hb : QStab.Paper.BB72BVBridge.is_X_only b = true) :
    ErrorVec.parity a b = false := by
  unfold ErrorVec.parity
  rw [QStab.Paper.BB72BVBridge.is_X_only_iff] at ha hb
  have hempty : (Finset.univ.filter fun i : Fin 72 =>
                  Pauli.anticommutes (a i) (b i) = true) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    rcases ha i with haI | haX
    · rw [haI]; simp [Pauli.anticommutes]
    · rcases hb i with hbI | hbX
      · rw [haX, hbI]; simp [Pauli.anticommutes]
      · rw [haX, hbX]; simp [Pauli.anticommutes]
  rw [hempty]
  simp

/-! ## Inductive existence: xContent of reachableE element is chain XOR -/

open QStab.Paper.GenericReachableBridge QStab.Paper.BB72ChainAttack
  QStab.Paper.BB72ChainCheck in
/-- For any `E ∈ reachableE bb_allHooks k`, there is a chain of length ≤ k of
    X-mech indices whose chain XOR equals `xContent E`. -/
theorem reachableE_xContent_chain :
    ∀ (k : Nat) (E : ErrorVec 72),
      E ∈ reachableE bb_allHooks k →
      ∃ chain : List (Fin 252),
        chain.length ≤ k ∧
        chain_xor chain = xContent E := by
  intro k
  induction k with
  | zero =>
    intro E hE
    -- reachableE 0 = [identity]
    simp [reachableE] at hE
    refine ⟨[], by simp, ?_⟩
    rw [hE, xContent_identity]
    show chain_xor [] = ErrorVec.identity 72
    rfl
  | succ k ih =>
    intro E hE
    -- reachableE (k+1) = prev ++ t01_ext ++ t2_ext
    simp only [reachableE, List.mem_append] at hE
    rcases hE with (hE_prev | hE_t01) | hE_t2
    · -- E ∈ prev (= reachableE k): IH gives chain of length ≤ k
      obtain ⟨chain, hlen, hxor⟩ := ih E hE_prev
      exact ⟨chain, by omega, hxor⟩
    · -- E ∈ t01_ext
      simp only [List.mem_flatMap, List.mem_map] at hE_t01
      obtain ⟨i, _hi_mem, p, hp_mem, e, he_prev, heq⟩ := hE_t01
      obtain ⟨chain', hlen, hxor⟩ := ih e he_prev
      subst heq
      -- p is one of X, Y, Z
      simp [List.mem_cons] at hp_mem
      rcases hp_mem with hpX | hpY | hpZ
      · -- p = X: prepend Type-0 X-mech at i
        subst hpX
        refine ⟨⟨i.val, by omega⟩ :: chain', by simp; omega, ?_⟩
        show chain_xor (⟨i.val, _⟩ :: chain') = xContent (ErrorVec.update e i .X)
        unfold chain_xor
        rw [bb_xMech_type0, xContent_update]
        unfold xContent_pauli
        rw [hxor]
      · -- p = Y: same chain (Y has same X-content as X)
        subst hpY
        refine ⟨⟨i.val, by omega⟩ :: chain', by simp; omega, ?_⟩
        show chain_xor (⟨i.val, _⟩ :: chain') = xContent (ErrorVec.update e i .Y)
        unfold chain_xor
        rw [bb_xMech_type0, xContent_update]
        unfold xContent_pauli
        rw [hxor]
      · -- p = Z: chain' suffices (xContent doesn't change)
        subst hpZ
        refine ⟨chain', by omega, ?_⟩
        rw [xContent_update]
        unfold xContent_pauli
        rw [update_I_eq, identity_mul, hxor]
    · -- E ∈ t2_ext
      simp only [List.mem_flatMap, List.mem_map] at hE_t2
      obtain ⟨h, hh_mem, e, he_prev, heq⟩ := hE_t2
      obtain ⟨chain', hlen, hxor⟩ := ih e he_prev
      obtain ⟨j, hj_eq⟩ := bb_xMech_hook h hh_mem
      subst heq
      refine ⟨j :: chain', by simp; omega, ?_⟩
      unfold chain_xor
      rw [hj_eq, xContent_mul]
      have hh_X_only : QStab.Paper.BB72BVBridge.is_X_only h = true := by
        rw [← hj_eq]; exact QStab.Paper.BB72BVBridge.bb_xMech_is_X_only j
      rw [xContent_fixes_X_only h hh_X_only, hxor]

/-! ## Bridge: bb_isSuccess (xContent E) = false → bb_isSuccess E = false -/

/-- For any stab index `i : Fin 72` with `i.val ≥ 36`, `i = zStabIdx ⟨i.val - 36, _⟩`. -/
theorem stab_idx_ge_36_eq_zStabIdx (i : Fin 72) (hi : 36 ≤ i.val) :
    i = QStab.Paper.BB72BVBridge.zStabIdx ⟨i.val - 36, by omega⟩ := by
  unfold QStab.Paper.BB72BVBridge.zStabIdx
  ext
  simp
  omega

/-- If `bb_isSuccess (xContent E) = false`, then `bb_isSuccess E = false`. -/
theorem bb_isSuccess_of_xContent_false (E : ErrorVec 72)
    (h : bb_isSuccess (xContent E) = false) : bb_isSuccess E = false := by
  unfold bb_isSuccess at h ⊢
  rw [Bool.and_eq_false_iff] at h ⊢
  rcases h with hstab | hlz
  · -- Some stab parity is true for xContent E
    left
    rw [List.all_eq_false] at hstab ⊢
    obtain ⟨i, hi_mem, hpari⟩ := hstab
    -- hpari : ¬(decide (parity = false) = true)
    have hpari_true : ErrorVec.parity (bb_stabilizers i) (xContent E) = true := by
      rw [Bool.not_eq_true, decide_eq_false_iff_not] at hpari
      cases h_par : ErrorVec.parity (bb_stabilizers i) (xContent E)
      · exact absurd h_par hpari
      · rfl
    -- Case on i.val
    by_cases hX : i.val < 36
    · -- X-stab case: contradicts since X-only × X-only = false
      exfalso
      have h_xonly_a : QStab.Paper.BB72BVBridge.is_X_only (bb_stabilizers i) = true :=
        QStab.Paper.BB72BVBridge.is_X_only_bb_xstab i hX
      have h_xonly_b : QStab.Paper.BB72BVBridge.is_X_only (xContent E) = true :=
        xContent_is_X_only E
      rw [parity_X_only_X_only _ _ h_xonly_a h_xonly_b] at hpari_true
      exact Bool.false_ne_true hpari_true
    · -- Z-stab case
      push_neg at hX
      let s : Fin 36 := ⟨i.val - 36, by omega⟩
      have heq : i = QStab.Paper.BB72BVBridge.zStabIdx s :=
        stab_idx_ge_36_eq_zStabIdx i hX
      refine ⟨i, hi_mem, ?_⟩
      rw [Bool.not_eq_true, decide_eq_false_iff_not]
      intro hpari_E_false
      have : ErrorVec.parity (bb_stabilizers i) (xContent E) = false := by
        rw [heq, parity_zstab_eq_xContent] at hpari_E_false
        rw [heq]; exact hpari_E_false
      rw [this] at hpari_true
      exact Bool.false_ne_true hpari_true
  · -- All L_Z parities are false for xContent E
    right
    rw [List.any_eq_false] at hlz ⊢
    intro l hl_mem
    have : ErrorVec.parity (bb_logicalZ_basis l) (xContent E) ≠ true :=
      hlz l hl_mem
    rw [← parity_lz_eq_xContent] at this
    exact this

/-! ## Final theorem: discharge bb_NZ_no_X_attack_below_6 axiom -/

open QStab.Paper.GenericReachableBridge QStab.Paper.BB72ChainAttack
  QStab.Paper.BB72ChainAttackFull in
/-- **Main result**: for any `E ∈ reachableE bb_allHooks 5`, `bb_isSuccess E = false`.
    This discharges the `bb_NZ_no_X_attack_below_6` axiom. -/
theorem bb_NZ_no_X_attack_below_6_proven :
    ∀ E ∈ reachableE bb_allHooks bb_code.C_budget, bb_isSuccess E = false := by
  intro E hE
  have hbudget : bb_code.C_budget = 5 := by rfl
  rw [hbudget] at hE
  obtain ⟨chain, hlen, hxor⟩ := reachableE_xContent_chain 5 E hE
  have h_chain_false : bb_chain_attack chain = false :=
    bb_chain_attack_le_5 chain hlen
  have h_xc_false : bb_isSuccess (xContent E) = false := by
    unfold bb_chain_attack at h_chain_false
    rw [hxor] at h_chain_false
    exact h_chain_false
  exact bb_isSuccess_of_xContent_false E h_xc_false

end QStab.Paper.BB72ReachableEBridge

/-! ## Re-export into `QStab.Paper.BB72Instance` namespace

The original axiom `bb_NZ_no_X_attack_below_6` and the headline theorem
`bb_NZ_d_circ_ge_6` were declared in the `QStab.Paper.BB72Instance`
namespace in `BB72Instance.lean`. The axiom has been removed; we
re-declare both names here as theorems using the proven version. -/

namespace QStab.Paper.BB72Instance

open QStab QStab.Paper.GenericReachableBridge

/-- **PROVEN** (formerly axiom): BB72 NZ X-side per-scheduling finite check.

    For all `E ∈ reachableE bb_allHooks bb_code.C_budget`, `bb_isSuccess E = false`.

    Discharged unconditionally via the chain-XOR reduction
    (`reachableE_xContent_chain`) composed with `bb_chain_attack_le_5`. -/
theorem bb_NZ_no_X_attack_below_6 :
    ∀ E ∈ reachableE bb_allHooks bb_code.C_budget, bb_isSuccess E = false :=
  QStab.Paper.BB72ReachableEBridge.bb_NZ_no_X_attack_below_6_proven

/--
**BB [[72, 12, 6]] with NZ-sorted scheduling: X-side operational d_circ ≥ 6.**

Combines the structural bridge invariant (`GenericReachableBridge`) with
the proven X-side check `bb_NZ_no_X_attack_below_6`. The result is a
fully-proved Lean theorem with no external axioms beyond standard Mathlib.

**Honest scope**: this is X-side d_circ ≥ 6. The theorem covers all
12 L_Z basis vectors (any X-only attack flipping any logical Z̄ rep).
For full d_circ ≥ 6 including L_X and L_Y attacks, an analogous Z-side
analysis would be needed.
-/
theorem bb_NZ_d_circ_ge_6 :
    ∀ (s : State bb_code),
      MultiStep bb_code (.active (State.init bb_code)) (.active s) →
      bb_isSuccess s.E_tilde = false := by
  intro s hreach
  exact nonSuccess_op_d_circ_ge_d
    bb_code bb_allHooks bb_hooks_bound bb_isSuccess
    bb_NZ_no_X_attack_below_6 s hreach

end QStab.Paper.BB72Instance
