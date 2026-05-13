import QStab.Paper.BB72BV
import QStab.Paper.BB72ChainCheck
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.ModEq

/-!
# BB72 BitVec ↔ ErrorVec bridge

Connects the fast `BB72BV` form (BitVec-based attack predicate, fast
`native_decide`) to the structural `BB72ChainCheck` form (ErrorVec-based
`bb_isSuccess`).

## What this file proves (this iteration: 1.10c.0 — building blocks)

  * `mech_x_bv i = ev_to_bv_x (bb_xMech i)` (per-mech, 252 cases).
  * `zstab_z_bv i = ev_to_bv_z (bb_stabilizers (i + 36))` (36 cases).
  * `lz_z_bv i = ev_to_bv_z (bb_logicalZ_basis i)` (12 cases).
  * `is_X_only (bb_xMech i)` for all 252 mechs.

Each is discharged by `native_decide` in <1 sec.

## What's pending (iteration 1.10c.1 — structural)

  * `is_X_only` preserved by `ErrorVec.mul`.
  * `ev_to_bv_x` is XOR-homomorphic on X-only ErrorVecs.
  * **Parity bridge**: for X-only E and Z-only zStab,
      `ErrorVec.parity zStab E = bv_parity (ev_to_bv_z zStab &&& ev_to_bv_x E)`.
  * Compose into the main bridge `bv_chain3_attack i j k = bb_isSuccess (bb_chain3XOR i j k)`.
  * Conclude `bb_chain_attack_k3` from `bb_chain_3_no_attack_bv`.
-/

set_option maxHeartbeats 4000000

namespace QStab.Paper.BB72BVBridge

open QStab QStab.Paper.BB72Instance QStab.Paper.BB72ChainCheck
open QStab.Paper.BB72BV ErrorVec

/-- BitVec representation of the X-content of an ErrorVec: bit `i` is set
    iff `E i = .X`. -/
def ev_to_bv_x (E : ErrorVec 72) : BitVec 72 :=
  Fin.foldr 72 (init := (0 : BitVec 72)) fun i acc =>
    if E i = Pauli.X then acc ||| ((1 : BitVec 72) <<< i.val) else acc

/-- BitVec representation of the Z-content of an ErrorVec. -/
def ev_to_bv_z (E : ErrorVec 72) : BitVec 72 :=
  Fin.foldr 72 (init := (0 : BitVec 72)) fun i acc =>
    if E i = Pauli.Z then acc ||| ((1 : BitVec 72) <<< i.val) else acc

/-- **Per-mech identity**: `mech_x_bv i = ev_to_bv_x (bb_xMech i)`.
    Discharged by `native_decide` over 252 cases. -/
theorem mech_x_bv_eq : ∀ i : Fin 252, mech_x_bv i = ev_to_bv_x (bb_xMech i) := by
  native_decide

/-- Z-stab indexing: BB72 Z-stabs are stored at indices 36..71 in
    `bb_stabilizers`. -/
def zStabIdx (i : Fin 36) : Fin 72 := ⟨i.val + 36, by omega⟩

/-- **Per-Z-stab identity**: `zstab_z_bv i = ev_to_bv_z (bb_stabilizers (zStabIdx i))`. -/
theorem zstab_z_bv_eq :
    ∀ i : Fin 36, zstab_z_bv i = ev_to_bv_z (bb_stabilizers (zStabIdx i)) := by
  native_decide

/-- **Per-L_Z identity**: `lz_z_bv i = ev_to_bv_z (bb_logicalZ_basis i)`. -/
theorem lz_z_bv_eq :
    ∀ i : Fin 12, lz_z_bv i = ev_to_bv_z (bb_logicalZ_basis i) := by
  native_decide

/-! ## X-only ErrorVec invariant

Chain XORs of X-mechs are X-only (every position is `.I` or `.X`).
This is preserved by `ErrorVec.mul` because `Pauli.mul` of {.I, .X}
stays in {.I, .X} (X*X = I, X*I = X, I*X = X, I*I = I).
-/

/-- A `Pauli` is X-only iff it is `.I` or `.X`. -/
def is_X_only_pauli : Pauli → Bool
  | .I => true
  | .X => true
  | _  => false

/-- An `ErrorVec 72` is X-only iff every position is `.I` or `.X`. -/
def is_X_only (E : ErrorVec 72) : Bool :=
  (List.finRange 72).all fun i => is_X_only_pauli (E i)

/-- Each mech is X-only. -/
theorem bb_xMech_is_X_only : ∀ i : Fin 252, is_X_only (bb_xMech i) = true := by
  native_decide

/-! ## Per-mech parity bridge

For each (Z-stab, mech) pair, the ErrorVec parity equals the BV parity
of the AND of supports. Proved by `native_decide` over 36 × 252 ≈ 9k
cases — each case evaluates a 72-position parity, totaling ~650k ops,
which native_decide handles easily.

Same for L_Z basis × mech (12 × 252 ≈ 3k cases).
-/

/-- Per-mech bridge for Z-stab parity. -/
theorem parity_zstab_mech_bridge :
    ∀ (s : Fin 36) (m : Fin 252),
      ErrorVec.parity (bb_stabilizers (zStabIdx s)) (bb_xMech m) =
        bv_parity (zstab_z_bv s &&& mech_x_bv m) := by
  native_decide

/-- Per-mech bridge for L_Z basis parity. -/
theorem parity_lz_mech_bridge :
    ∀ (l : Fin 12) (m : Fin 252),
      ErrorVec.parity (bb_logicalZ_basis l) (bb_xMech m) =
        bv_parity (lz_z_bv l &&& mech_x_bv m) := by
  native_decide

/-! ## Pointwise homomorphism: `anticommutes` is XOR-bilinear (Z-only / X-only)

For z ∈ {.I, .Z} and a, b ∈ {.I, .X}:
  `anticommutes z (mul a b) = (anticommutes z a) XOR (anticommutes z b)`.

Proved by case analysis (8 cases). -/

theorem anticommutes_mul_xor_zx (z a b : Pauli) :
    (z = .I ∨ z = .Z) → (a = .I ∨ a = .X) → (b = .I ∨ b = .X) →
    Pauli.anticommutes z (Pauli.mul a b) =
      xor (Pauli.anticommutes z a) (Pauli.anticommutes z b) := by
  intro hz ha hb
  rcases hz with hz | hz <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    subst hz <;> subst ha <;> subst hb <;> rfl

/-! ## ErrorVec parity is XOR-homomorphic for Z-only stab × X-only operands

The key chain-level homomorphism. From this and `parity_zstab_mech_bridge`,
we can compose the K-mech parity bridge by induction on K.

Two abstract facts feed into the homomorphism proof:
  1. `anticommutes_mul_xor_zx` (above) — pointwise Pauli homomorphism.
  2. `filter_xor_card_mod_two` (next iteration) — symmetric difference
     cardinality mod 2.

This iteration commits the auxiliary `is_X_only_iff` and `is_Z_only`
lemmas; the cardinality lemma is deferred. -/

/-- Convert `is_X_only` Bool to a per-position disjunction. -/
theorem is_X_only_iff (E : ErrorVec 72) :
    is_X_only E = true ↔ ∀ i : Fin 72, E i = .I ∨ E i = .X := by
  unfold is_X_only
  rw [List.all_eq_true]
  refine ⟨fun h i => ?_, fun h i _ => ?_⟩
  · have := h i (List.mem_finRange i)
    cases hE : E i <;> simp_all [is_X_only_pauli]
  · have := h i
    rcases this with hI | hX
    · simp [hI, is_X_only_pauli]
    · simp [hX, is_X_only_pauli]

/-- A `Pauli` is Z-only iff it is `.I` or `.Z`. -/
def is_Z_only_pauli : Pauli → Bool
  | .I => true
  | .Z => true
  | _  => false

/-- An `ErrorVec 72` is Z-only iff every position is `.I` or `.Z`. -/
def is_Z_only (E : ErrorVec 72) : Bool :=
  (List.finRange 72).all fun i => is_Z_only_pauli (E i)

theorem is_Z_only_iff (E : ErrorVec 72) :
    is_Z_only E = true ↔ ∀ i : Fin 72, E i = .I ∨ E i = .Z := by
  unfold is_Z_only
  rw [List.all_eq_true]
  refine ⟨fun h i => ?_, fun h i _ => ?_⟩
  · have := h i (List.mem_finRange i)
    cases hE : E i <;> simp_all [is_Z_only_pauli]
  · have := h i
    rcases this with hI | hZ
    · simp [hI, is_Z_only_pauli]
    · simp [hZ, is_Z_only_pauli]

/-! ## Cardinality of XOR-filter is XOR-homomorphic mod 2

Sum-based proof: avoids the if-then-else reduction issues of Finset.induction.
We show `(filter P).card = Σ (P i).toNat` and use modular arithmetic.
-/

/-- The cardinality of a Bool-predicate filter equals the sum of `Bool.toNat`. -/
theorem card_filter_bool_eq_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → Bool) :
    (s.filter (fun i => f i = true)).card = ∑ i ∈ s, (f i).toNat := by
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases f i <;> rfl

/-- Pointwise: `(xor a b).toNat ≡ a.toNat + b.toNat (mod 2)`. -/
theorem Bool.xor_toNat_mod_two (a b : Bool) :
    (xor a b).toNat % 2 = (a.toNat + b.toNat) % 2 := by
  cases a <;> cases b <;> rfl

/-- **Cardinality of a XOR-filter is XOR-homomorphic mod 2.** -/
theorem card_filter_xor_mod_two {α : Type*} [DecidableEq α]
    (s : Finset α) (f g : α → Bool) :
    (s.filter (fun i => xor (f i) (g i) = true)).card % 2 =
      ((s.filter (fun i => f i = true)).card +
       (s.filter (fun i => g i = true)).card) % 2 := by
  rw [card_filter_bool_eq_sum, card_filter_bool_eq_sum, card_filter_bool_eq_sum]
  rw [← Finset.sum_add_distrib]
  exact Nat.ModEq.sum (fun i _ => Bool.xor_toNat_mod_two (f i) (g i))

/-- Connector: (a+b) odd iff exactly one of a, b is odd. -/
theorem add_mod_two_eq_xor (a b : Nat) :
    ((a + b) % 2 == 1) = xor (a % 2 == 1) (b % 2 == 1) := by
  have ha := Nat.mod_two_eq_zero_or_one a
  have hb := Nat.mod_two_eq_zero_or_one b
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [Nat.add_mod, ha, hb]

/-- **`ErrorVec.parity` is XOR-homomorphic for Z-only stab × X-only operands.** -/
theorem parity_mul_xor_zx (z a b : ErrorVec 72)
    (hz : is_Z_only z = true) (ha : is_X_only a = true) (hb : is_X_only b = true) :
    ErrorVec.parity z (ErrorVec.mul a b) =
      xor (ErrorVec.parity z a) (ErrorVec.parity z b) := by
  unfold ErrorVec.parity ErrorVec.mul
  rw [is_Z_only_iff] at hz
  rw [is_X_only_iff] at ha
  rw [is_X_only_iff] at hb
  -- Pointwise: anti(z i, mul (a i) (b i)) = xor (anti (z i) (a i)) (anti (z i) (b i)).
  have hfilter_eq : (Finset.univ.filter fun i : Fin 72 =>
        Pauli.anticommutes (z i) (Pauli.mul (a i) (b i)) = true) =
      Finset.univ.filter fun i : Fin 72 =>
        xor (Pauli.anticommutes (z i) (a i)) (Pauli.anticommutes (z i) (b i)) = true := by
    apply Finset.filter_congr
    intro i _
    rw [anticommutes_mul_xor_zx (z i) (a i) (b i) (hz i) (ha i) (hb i)]
  show ((Finset.univ.filter fun i : Fin 72 =>
        Pauli.anticommutes (z i) (Pauli.mul (a i) (b i)) = true).card % 2 == 1) =
      xor ((Finset.univ.filter fun i : Fin 72 =>
        Pauli.anticommutes (z i) (a i) = true).card % 2 == 1)
        ((Finset.univ.filter fun i : Fin 72 =>
          Pauli.anticommutes (z i) (b i) = true).card % 2 == 1)
  rw [hfilter_eq, card_filter_xor_mod_two, add_mod_two_eq_xor]

/-! ## Z-only invariants for stabs and logicals (data-level identities) -/

theorem is_Z_only_bb_zstab :
    ∀ i : Fin 36, is_Z_only (bb_stabilizers (zStabIdx i)) = true := by
  native_decide

theorem is_Z_only_bb_lz :
    ∀ l : Fin 12, is_Z_only (bb_logicalZ_basis l) = true := by
  native_decide

/-! ## X-only is preserved under `ErrorVec.mul` -/

theorem mul_preserves_X_only (a b : ErrorVec 72)
    (ha : is_X_only a = true) (hb : is_X_only b = true) :
    is_X_only (ErrorVec.mul a b) = true := by
  rw [is_X_only_iff] at ha hb
  rw [is_X_only_iff]
  intro i
  rcases ha i with hai | hai <;> rcases hb i with hbi | hbi <;>
    simp [ErrorVec.mul, hai, hbi, Pauli.mul]

/-! ## BV parity is XOR-homomorphic -/

/-- Helper: foldr over a list of bool-valued XORs distributes. -/
theorem List.foldr_xor_distrib {α : Type*} (l : List α) (f g : α → Bool) :
    l.foldr (fun i acc => xor (xor (f i) (g i)) acc) false =
      xor (l.foldr (fun i acc => xor (f i) acc) false)
          (l.foldr (fun i acc => xor (g i) acc) false) := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldr_cons, ih]
    -- Goal: xor (xor (f head) (g head)) (xor X Y) = xor (xor (f head) X) (xor (g head) Y)
    -- where X = foldr ... f tail, Y = foldr ... g tail.
    rw [Bool.xor_assoc, Bool.xor_assoc, Bool.xor_left_comm (g head)]

theorem bv_parity_xor (e1 e2 : BitVec 72) :
    bv_parity (e1 ^^^ e2) = xor (bv_parity e1) (bv_parity e2) := by
  unfold bv_parity
  have hpw : ∀ i, ((e1 ^^^ e2).getLsbD i) = xor (e1.getLsbD i) (e2.getLsbD i) := by
    intro i; exact BitVec.getLsbD_xor
  conv_lhs =>
    rw [show (fun i acc => xor ((e1 ^^^ e2).getLsbD i) acc) =
            (fun i acc => xor (xor (e1.getLsbD i) (e2.getLsbD i)) acc) from by
          funext i acc; rw [hpw]]
  exact List.foldr_xor_distrib (List.range 72) e1.getLsbD e2.getLsbD

/-! ## BitVec AND-XOR distributivity -/

theorem BitVec.and_xor_distrib_left {w : Nat} (x y z : BitVec w) :
    x &&& (y ^^^ z) = (x &&& y) ^^^ (x &&& z) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp [BitVec.getLsbD_and, BitVec.getLsbD_xor, Bool.and_xor_distrib_left]

/-! ## K=3 chain parity bridge: Z-stab side -/

/-- For Z-stab `s` and 3-mech chain (i,j,k), the ErrorVec parity equals
    the BV parity of (Z-stab support) AND (chain X-support). -/
theorem parity_zstab_chain3_bridge (s : Fin 36) (i j k : Fin 252) :
    ErrorVec.parity (bb_stabilizers (zStabIdx s)) (bb_chain3XOR i j k) =
    bv_parity (zstab_z_bv s &&& (mech_x_bv i ^^^ mech_x_bv j ^^^ mech_x_bv k)) := by
  unfold bb_chain3XOR
  -- LHS = parity zStab (mul (xMech i) (mul (xMech j) (xMech k)))
  -- Apply parity_mul_xor_zx twice.
  have hi := bb_xMech_is_X_only i
  have hj := bb_xMech_is_X_only j
  have hk := bb_xMech_is_X_only k
  have hjk := mul_preserves_X_only _ _ hj hk
  have hZ := is_Z_only_bb_zstab s
  rw [parity_mul_xor_zx _ _ _ hZ hi hjk]
  rw [parity_mul_xor_zx _ _ _ hZ hj hk]
  -- Now: xor (parity zStab xMech_i) (xor (parity zStab xMech_j) (parity zStab xMech_k))
  rw [parity_zstab_mech_bridge, parity_zstab_mech_bridge, parity_zstab_mech_bridge]
  -- = xor (bv_parity (z_supp &&& mech_i_supp)) (xor (bv_parity (z_supp &&& mech_j_supp)) (bv_parity (z_supp &&& mech_k_supp)))
  rw [← bv_parity_xor, ← bv_parity_xor]
  -- = bv_parity ((z &&& m_i) ^^^ ((z &&& m_j) ^^^ (z &&& m_k)))
  rw [← BitVec.and_xor_distrib_left, ← BitVec.and_xor_distrib_left,
      ← BitVec.xor_assoc]

/-- Same for L_Z basis. -/
theorem parity_lz_chain3_bridge (l : Fin 12) (i j k : Fin 252) :
    ErrorVec.parity (bb_logicalZ_basis l) (bb_chain3XOR i j k) =
    bv_parity (lz_z_bv l &&& (mech_x_bv i ^^^ mech_x_bv j ^^^ mech_x_bv k)) := by
  unfold bb_chain3XOR
  have hi := bb_xMech_is_X_only i
  have hj := bb_xMech_is_X_only j
  have hk := bb_xMech_is_X_only k
  have hjk := mul_preserves_X_only _ _ hj hk
  have hZ := is_Z_only_bb_lz l
  rw [parity_mul_xor_zx _ _ _ hZ hi hjk]
  rw [parity_mul_xor_zx _ _ _ hZ hj hk]
  rw [parity_lz_mech_bridge, parity_lz_mech_bridge, parity_lz_mech_bridge]
  rw [← bv_parity_xor, ← bv_parity_xor]
  rw [← BitVec.and_xor_distrib_left, ← BitVec.and_xor_distrib_left,
      ← BitVec.xor_assoc]

/-! ## X-stab × X-only triviality -/

/-- For X-only z and X-only e, parity is always false. -/
theorem parity_xx_zero (z e : ErrorVec 72)
    (hz : is_X_only z = true) (he : is_X_only e = true) :
    ErrorVec.parity z e = false := by
  unfold ErrorVec.parity
  rw [is_X_only_iff] at hz he
  have hempty : (Finset.univ.filter fun i : Fin 72 =>
        Pauli.anticommutes (z i) (e i)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    rcases hz i with hz' | hz' <;> rcases he i with he' | he' <;>
      rw [hz', he'] <;> decide
  rw [hempty]
  simp

/-- Each X-stab is X-only. -/
theorem is_X_only_bb_xstab :
    ∀ s : Fin 72, s.val < 36 → is_X_only (bb_stabilizers s) = true := by
  decide

/-! ## Some-L_Z side bridge (Bool-level) -/

/-- The L_Z `Bool`-coerced predicate is the same on both ErrorVec and BV form.
    Useful as a building block for the full `bb_isSuccess`-`bv_chain3_attack`
    bridge (which also needs the all-stab side, deferred). -/
theorem any_lz_chain3_eq_bv (i j k : Fin 252) :
    ((List.finRange 12).any fun l => ErrorVec.parity (bb_logicalZ_basis l) (bb_chain3XOR i j k)) =
    ((List.finRange 12).any fun l =>
      bv_parity (lz_z_bv l &&& (mech_x_bv i ^^^ mech_x_bv j ^^^ mech_x_bv k)) = true) := by
  apply List.any_congr rfl
  intro l
  rw [parity_lz_chain3_bridge]
  cases bv_parity (lz_z_bv l &&& (mech_x_bv i ^^^ mech_x_bv j ^^^ mech_x_bv k)) <;> rfl

/-! ## bb_chain_3_no_attack: ErrorVec K=3 chain attack predicate is always false -/

/-- **No 3-mech chain is a successful X-side attack.** ErrorVec form.

    Proven via composition: if it WERE a success, then `bb_chain_3_no_attack_bv`
    is contradicted via the chain bridges. -/
theorem bb_chain_3_no_attack :
    ∀ i j k : Fin 252, bb_isSuccess (bb_chain3XOR i j k) = false := by
  intro i j k
  have hbv : bv_chain3_attack i j k = false := bb_chain_3_no_attack_bv i j k
  unfold bv_chain3_attack bv_attack at hbv
  unfold bb_isSuccess
  rw [Bool.and_eq_false_iff] at hbv
  rcases hbv with hAbv | hBbv
  · -- A_bv = false: some Z-stab BV-parity is true. Lift to ErrorVec via zStabIdx.
    apply Bool.and_eq_false_iff.mpr
    left
    rw [List.all_eq_false]
    rw [List.all_eq_false] at hAbv
    obtain ⟨s_bv, _, hs_bv⟩ := hAbv
    -- hs_bv : ¬ (bv_parity (zstab_z_bv s_bv &&& ...) = false)
    -- Witness for the ErrorVec all-72: zStabIdx s_bv ∈ Fin 72.
    refine ⟨zStabIdx s_bv, List.mem_finRange _, ?_⟩
    -- Goal: ¬ (parity (bb_stab (zStabIdx s_bv)) (chain3XOR) = false)
    rw [parity_zstab_chain3_bridge]
    exact hs_bv
  · -- B_bv = false: all L_Z BV-parities are false → all ErrorVec parities false → any = false.
    apply Bool.and_eq_false_iff.mpr
    right
    rw [any_lz_chain3_eq_bv]
    exact hBbv

end QStab.Paper.BB72BVBridge
