import QStab.Paper.BB72BVData

/-!
# BB72 X-side static-DEM check: BitVec form

Recasts the chain attack predicate via 72-bit BitVec X-supports
(rather than `Fin 72 → Pauli` ErrorVec). The BitVec form allows
`native_decide` to use efficient bitwise ops, dramatically faster
than ErrorVec's Finset-based parity computation.

This file is a **scaling experiment**: discharge K=2, K=3, (K=4?)
chain-attack via `native_decide` on BitVec, bypassing the SAT bridge
where feasible.

## Predicate

`bv_attack e` (for `e : BitVec 72` = chain XOR's X-content):
  * For all 36 Z-stabs `s`: parity (s &&& e) = 0.
  * Some L_Z basis `lz`: parity (lz &&& e) = 1.

`parity x = x.toNat.bit count % 2`. We compute via `Nat.testBit` fold.
-/

set_option maxHeartbeats 4000000

namespace QStab.Paper.BB72BV

/-- BitVec parity: XOR of all 72 bits of `x`. -/
def bv_parity (x : BitVec 72) : Bool :=
  (List.range 72).foldr (fun i acc => xor (x.getLsbD i) acc) false

/-- Whether `e` (chain XOR X-content) is a successful X-side attack. -/
def bv_attack (e : BitVec 72) : Bool :=
  ((List.finRange 36).all fun i => bv_parity (zstab_z_bv i &&& e) = false)
  &&
  ((List.finRange 12).any fun i => bv_parity (lz_z_bv i &&& e) = true)

/-- Chain XOR via foldr in BitVec form. -/
def bv_chain_xor : List (Fin 252) → BitVec 72
  | []        => 0
  | i :: rest => mech_x_bv i ^^^ bv_chain_xor rest

/-! ## K=2: scaling experiment -/

/-- 2-mech chain attack predicate (tuple form for native_decide). -/
def bv_chain2_attack (i j : Fin 252) : Bool :=
  bv_attack (mech_x_bv i ^^^ mech_x_bv j)

/-- **No 2-mech chain is a successful X-side attack.** (BitVec form.) -/
theorem bb_chain_2_no_attack_bv :
    ∀ i j : Fin 252, bv_chain2_attack i j = false := by
  native_decide

/-! ## K=3: scaling experiment -/

/-- 3-mech chain attack predicate (tuple form). -/
def bv_chain3_attack (i j k : Fin 252) : Bool :=
  bv_attack (mech_x_bv i ^^^ mech_x_bv j ^^^ mech_x_bv k)

/-- **No 3-mech chain is a successful X-side attack.** (BitVec form.)

    Brute-force enumeration over 252³ ≈ 16M tuples via `native_decide`.
    Estimated build time ~30 min based on K=2 scaling (6.9 s × 252). -/
theorem bb_chain_3_no_attack_bv :
    ∀ i j k : Fin 252, bv_chain3_attack i j k = false := by
  native_decide

end QStab.Paper.BB72BV
