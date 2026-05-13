import QStab.Paper.BB72ReachableEBridge
import QStab.Paper.BB72JointInstance

/-!
# `reachableE` → chain-XOR reduction (Z-side)

Mirror of `BB72ReachableEBridge` for the Z-side. Defines `zContent` (the
Z-only projection: Z/Y → Z, I/X → I), the Z-mech enumeration, and the
parity equivalences for X-only stabs and L_X basis vectors.

The final discharge of `bb_NZ_no_Z_attack_below_6` requires the Z-side
chain-attack k≤5 theorem (analogous to `bb_chain_attack_le_5`), which
needs its own native_decide enumeration in subsequent files. This file
provides the structural bridge half.

## Structural reduction

For `E : ErrorVec 72`, define `zContent E : ErrorVec 72` as the Z-only
projection: E[i] ∈ {.Z, .Y} → .Z; E[i] ∈ {.I, .X} → .I.

Properties (proved here):

1. `zContent` is a homomorphism w.r.t. ErrorVec.mul.
2. `zContent` fixes Z-only ErrorVecs (in particular, all Z-mechs).
3. For X-only stab `x` and any `E`, parity vs E equals parity vs zContent E.
4. `bb_zMech : Fin 252 → ErrorVec 72` enumerates 72 Type-0 Z + 180 Z-hooks.
-/

namespace QStab.Paper.BB72ReachableEBridgeZ

open QStab QStab.Paper.BB72Instance QStab.Paper.BB72JointInstance ErrorVec

/-- Per-Pauli Z-content projection: Z and Y both have Z-content Z; I and X have Z-content I. -/
def zContent_pauli : Pauli → Pauli
  | .X => .I
  | .Y => .Z
  | .I => .I
  | .Z => .Z

/-- Z-only projection of an ErrorVec. -/
def zContent (E : ErrorVec 72) : ErrorVec 72 := fun i => zContent_pauli (E i)

/-- Z-content respects Pauli multiplication (Klein-four homomorphism onto {I, Z}). -/
theorem zContent_pauli_mul (p q : Pauli) :
    zContent_pauli (Pauli.mul p q) =
      Pauli.mul (zContent_pauli p) (zContent_pauli q) := by
  cases p <;> cases q <;> rfl

/-- zContent is an ErrorVec.mul homomorphism. -/
theorem zContent_mul (a b : ErrorVec 72) :
    zContent (ErrorVec.mul a b) = ErrorVec.mul (zContent a) (zContent b) := by
  unfold zContent ErrorVec.mul
  funext i
  exact zContent_pauli_mul (a i) (b i)

/-- zContent fixes the identity. -/
theorem zContent_identity :
    zContent (ErrorVec.identity 72) = ErrorVec.identity 72 := by
  unfold zContent ErrorVec.identity zContent_pauli
  funext i
  rfl

/-! ## Z-only invariant: predicate and basic lemmas (parallel to is_X_only) -/

/-- Per-Pauli "is Z-only" check: only `.I` and `.Z` qualify. -/
def is_Z_only_pauli : Pauli → Bool
  | .I => true
  | .Z => true
  | .X => false
  | .Y => false

/-- An ErrorVec is Z-only if every position is `.I` or `.Z`. -/
def is_Z_only_ev (E : ErrorVec 72) : Bool :=
  (List.finRange 72).all fun i => is_Z_only_pauli (E i)

theorem is_Z_only_ev_iff (E : ErrorVec 72) :
    is_Z_only_ev E = true ↔ ∀ i : Fin 72, E i = .I ∨ E i = .Z := by
  unfold is_Z_only_ev
  constructor
  · intro h i
    simp [List.all_eq_true] at h
    have := h i
    cases hE : E i <;> simp_all [is_Z_only_pauli]
  · intro h
    simp [List.all_eq_true]
    intro i
    rcases h i with hI | hZ
    · simp [hI, is_Z_only_pauli]
    · simp [hZ, is_Z_only_pauli]

/-- zContent of an ErrorVec is Z-only. -/
theorem zContent_is_Z_only (E : ErrorVec 72) :
    is_Z_only_ev (zContent E) = true := by
  rw [is_Z_only_ev_iff]
  intro i
  unfold zContent zContent_pauli
  cases E i <;> simp

/-- zContent fixes Z-only ErrorVecs. -/
theorem zContent_fixes_Z_only (E : ErrorVec 72)
    (h : is_Z_only_ev E = true) : zContent E = E := by
  rw [is_Z_only_ev_iff] at h
  funext i
  rcases h i with hI | hZ
  · unfold zContent zContent_pauli; rw [hI]
  · unfold zContent zContent_pauli; rw [hZ]

/-! ## Parity equivalence: X-only stab × E = X-only stab × zContent E -/

/-- For X-only stab `x` and any `E`, parity vs E equals parity vs zContent E.
    (X anticommutes with Z and Y; commutes with I and X. Both checks pick
    up positions where E i ∈ {Y, Z} = same as zContent E i = Z.) -/
theorem parity_x_only_eq_zContent (x E : ErrorVec 72)
    (hx : QStab.Paper.BB72BVBridge.is_X_only x = true) :
    ErrorVec.parity x E = ErrorVec.parity x (zContent E) := by
  unfold ErrorVec.parity
  have hf : (Finset.univ.filter fun i : Fin 72 =>
                Pauli.anticommutes (x i) (E i) = true)
          = Finset.univ.filter fun i : Fin 72 =>
                Pauli.anticommutes (x i) (zContent E i) = true := by
    apply Finset.filter_congr
    intro i _
    rw [QStab.Paper.BB72BVBridge.is_X_only_iff] at hx
    rcases hx i with hxI | hxX
    · rw [hxI]; simp [Pauli.anticommutes]
    · rw [hxX]
      unfold zContent zContent_pauli
      generalize E i = e
      cases e <;> simp [Pauli.anticommutes]
  rw [hf]

/-! ## Z-mech enumeration (parallel to bb_xMech) -/

/-- Index `i : Fin 252`:
    * `i.val < 72`: Type-0 Z mech at qubit `i.val`.
    * `i.val ≥ 72`: Z-hook number `i.val - 72` from `bb_allHooksZ`. -/
def bb_zMech (i : Fin 252) : ErrorVec 72 :=
  if h : i.val < 72 then
    ErrorVec.update (ErrorVec.identity 72) ⟨i.val, by omega⟩ .Z
  else
    bb_allHooksZ.getD (i.val - 72) (ErrorVec.identity 72)

/-- bb_allHooksZ has length 180. -/
theorem bb_allHooksZ_length : bb_allHooksZ.length = 180 := by native_decide

/-- Each Z-mech is Z-only. -/
theorem bb_zMech_is_Z_only : ∀ i : Fin 252, is_Z_only_ev (bb_zMech i) = true := by
  native_decide

/-- zContent fixes the 252 Z-mechs. -/
theorem zContent_zMech (i : Fin 252) :
    zContent (bb_zMech i) = bb_zMech i :=
  zContent_fixes_Z_only _ (bb_zMech_is_Z_only i)

/-- Any Z-hook in bb_allHooksZ corresponds to a Z-mech index ≥ 72. -/
theorem bb_zMech_hook (h : ErrorVec 72) (hh : h ∈ bb_allHooksZ) :
    ∃ j : Fin 252, bb_zMech j = h := by
  obtain ⟨n, hn_lt, hn_get⟩ := List.getElem_of_mem hh
  rw [bb_allHooksZ_length] at hn_lt
  refine ⟨⟨72 + n, by omega⟩, ?_⟩
  unfold bb_zMech
  have hge : ¬ (72 + n < 72) := by omega
  simp only [hge, ↓reduceDIte]
  have hidx : 72 + n - 72 = n := by omega
  rw [hidx, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by rw [bb_allHooksZ_length]; exact hn_lt)]
  exact hn_get

/-- Each L_X basis vector is X-only. -/
theorem is_X_only_bb_lx :
    ∀ l : Fin 12, QStab.Paper.BB72BVBridge.is_X_only (bb_logicalX_basis l) = true := by
  native_decide

/-- Specialization: for any X-stab (i.val < 36), parity vs E equals parity vs zContent E. -/
theorem parity_xstab_eq_zContent (i : Fin 72) (hi : i.val < 36) (E : ErrorVec 72) :
    ErrorVec.parity (bb_stabilizers i) E =
      ErrorVec.parity (bb_stabilizers i) (zContent E) :=
  parity_x_only_eq_zContent _ _ (QStab.Paper.BB72BVBridge.is_X_only_bb_xstab i hi)

/-- Specialization: for any L_X basis vector, parity vs E equals parity vs zContent E. -/
theorem parity_lx_eq_zContent (l : Fin 12) (E : ErrorVec 72) :
    ErrorVec.parity (bb_logicalX_basis l) E =
      ErrorVec.parity (bb_logicalX_basis l) (zContent E) :=
  parity_x_only_eq_zContent _ _ (is_X_only_bb_lx l)

/-! ## Z-only × Z-only parity is zero -/

theorem parity_Z_only_Z_only (a b : ErrorVec 72)
    (ha : is_Z_only_ev a = true)
    (hb : is_Z_only_ev b = true) :
    ErrorVec.parity a b = false := by
  unfold ErrorVec.parity
  rw [is_Z_only_ev_iff] at ha hb
  have hempty : (Finset.univ.filter fun i : Fin 72 =>
                  Pauli.anticommutes (a i) (b i) = true) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    rcases ha i with haI | haZ
    · rw [haI]; simp [Pauli.anticommutes]
    · rcases hb i with hbI | hbZ
      · rw [haZ, hbI]; simp [Pauli.anticommutes]
      · rw [haZ, hbZ]; simp [Pauli.anticommutes]
  rw [hempty]
  simp

/-! ## Update / singleton lemmas for Z-side -/

/-- Type-0 Z-mech at qubit i (i : Fin 72) equals the singleton Z-update of identity. -/
theorem bb_zMech_type0 (i : Fin 72) :
    bb_zMech ⟨i.val, by omega⟩ =
      ErrorVec.update (ErrorVec.identity 72) i .Z := by
  unfold bb_zMech
  simp [i.isLt]

/-- xContent of a singleton Z-update: at position i, gives Z if p produces Z, else I. -/
theorem zContent_singleton (i : Fin 72) (p : Pauli) :
    zContent (ErrorVec.update (ErrorVec.identity 72) i p) =
      ErrorVec.update (ErrorVec.identity 72) i (zContent_pauli p) := by
  unfold zContent ErrorVec.update ErrorVec.identity
  funext j
  by_cases hji : j = i
  · subst hji
    simp [QStab.Paper.BB72ReachableEBridge.Pauli_mul_I_right]
  · simp [Function.update_of_ne hji]; rfl

/-- zContent under update: factor out as `mul (singleton zContent_pauli p) (zContent e)`. -/
theorem zContent_update (e : ErrorVec 72) (i : Fin 72) (p : Pauli) :
    zContent (ErrorVec.update e i p) =
      ErrorVec.mul
        (ErrorVec.update (ErrorVec.identity 72) i (zContent_pauli p))
        (zContent e) := by
  rw [QStab.Paper.BB72ReachableEBridge.update_eq_mul_singleton, zContent_mul, zContent_singleton]

/-! ## Z-side chain XOR -/

/-- Chain XOR for a list of Z-mech indices. -/
def chain_xor_Z : List (Fin 252) → ErrorVec 72
  | []        => ErrorVec.identity 72
  | i :: rest => ErrorVec.mul (bb_zMech i) (chain_xor_Z rest)

/-! ## Inductive existence: zContent of reachableE element is Z-side chain XOR -/

open QStab.Paper.GenericReachableBridge QStab.Paper.BB72ReachableEBridge in
/-- For any `E ∈ reachableE bb_allHooksZ k`, there is a chain of length ≤ k of
    Z-mech indices whose chain XOR equals `zContent E`. -/
theorem reachableE_zContent_chain :
    ∀ (k : Nat) (E : ErrorVec 72),
      E ∈ reachableE bb_allHooksZ k →
      ∃ chain : List (Fin 252),
        chain.length ≤ k ∧
        chain_xor_Z chain = zContent E := by
  intro k
  induction k with
  | zero =>
    intro E hE
    simp [reachableE] at hE
    refine ⟨[], by simp, ?_⟩
    rw [hE, zContent_identity]
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
      · -- p = X: zContent_pauli X = I → no Z-mech contribution
        subst hpX
        refine ⟨chain', by omega, ?_⟩
        rw [zContent_update]
        unfold zContent_pauli
        rw [QStab.Paper.BB72ReachableEBridge.update_I_eq,
            QStab.Paper.BB72ReachableEBridge.identity_mul, hxor]
      · -- p = Y: zContent_pauli Y = Z → prepend Type-0 Z-mech at i
        subst hpY
        refine ⟨⟨i.val, by omega⟩ :: chain', by simp; omega, ?_⟩
        show chain_xor_Z (⟨i.val, _⟩ :: chain') = zContent (ErrorVec.update e i .Y)
        unfold chain_xor_Z
        rw [bb_zMech_type0, zContent_update]
        unfold zContent_pauli
        rw [hxor]
      · -- p = Z: prepend Type-0 Z-mech at i
        subst hpZ
        refine ⟨⟨i.val, by omega⟩ :: chain', by simp; omega, ?_⟩
        show chain_xor_Z (⟨i.val, _⟩ :: chain') = zContent (ErrorVec.update e i .Z)
        unfold chain_xor_Z
        rw [bb_zMech_type0, zContent_update]
        unfold zContent_pauli
        rw [hxor]
    · simp only [List.mem_flatMap, List.mem_map] at hE_t2
      obtain ⟨h, hh_mem, e, he_prev, heq⟩ := hE_t2
      obtain ⟨chain', hlen, hxor⟩ := ih e he_prev
      obtain ⟨j, hj_eq⟩ := bb_zMech_hook h hh_mem
      subst heq
      refine ⟨j :: chain', by simp; omega, ?_⟩
      unfold chain_xor_Z
      rw [hj_eq, zContent_mul]
      have hh_Z_only : is_Z_only_ev h = true := by
        rw [← hj_eq]; exact bb_zMech_is_Z_only j
      rw [zContent_fixes_Z_only h hh_Z_only, hxor]

end QStab.Paper.BB72ReachableEBridgeZ
