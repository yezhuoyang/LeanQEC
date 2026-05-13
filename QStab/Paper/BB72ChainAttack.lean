import QStab.Paper.BB72ChainCheck
import QStab.Paper.BB72BVBridge

/-!
# BB72 chain-attack predicate (uniform K, list-based)

This file gives a uniform list-based formulation of the BB72 chain-attack
predicate.

`bb_chain_attack chain` says: the XOR of mechs along `chain` (a list of
mech indices in `Fin 252`) is a successful X-side attack — that is,
its parity vs every Z-stab is zero AND its parity vs some L_Z basis
vector is one.

## Discharge status

| K | Status | Method |
|---|---|---|
| 0 | ✅ proven | identity ErrorVec → no attack |
| 1 | ✅ proven | `bb_chain_1_no_attack` (`native_decide` on ErrorVec) |
| 2 | ✅ proven | `bb_chain_2_no_attack` (`native_decide` on ErrorVec) |
| 3 | ✅ proven | `bb_chain_3_no_attack` via BV `native_decide` + bridge |
| 4 | ⏳ hypothesis | needs SAT-encoding bridge |
| 5 | ⏳ hypothesis | needs SAT-encoding bridge |

## Composite theorems

  * `bb_chain_attack_le_3` — unconditional, K ≤ 3.
  * `bb_chain_attack_le_5_of_k4_k5` — conditional on K=4, K=5 hypotheses.

## Path to discharge K = 4, K = 5

The SAT-level theorems `bb72_k{4,5}_unsat` (in `BB72k{4,5}SAT.lean`) prove
the corresponding CNF instances are unsatisfiable. The remaining bridge
work — turning CNF Unsat into "no length-K chain attack" — is documented
in `notes/sat_bridge_design.md`.
-/

namespace QStab.Paper.BB72ChainAttack

open QStab QStab.Paper.BB72Instance QStab.Paper.BB72ChainCheck

/-- Chain XOR for a list of mech indices (foldr by `ErrorVec.mul`). -/
def chain_xor : List (Fin 252) → ErrorVec 72
  | []        => ErrorVec.identity 72
  | i :: rest => ErrorVec.mul (bb_xMech i) (chain_xor rest)

/-- A chain is a successful X-side attack iff its XOR commutes with all
    Z-stabs AND has nonzero parity for some L_Z basis vector. -/
def bb_chain_attack (chain : List (Fin 252)) : Bool :=
  bb_isSuccess (chain_xor chain)

/-! ## Useful identity: `mul e (identity n) = e` -/

theorem ErrorVec_mul_identity_right {n : Nat} (e : ErrorVec n) :
    ErrorVec.mul e (ErrorVec.identity n) = e := by
  unfold ErrorVec.mul ErrorVec.identity
  funext q
  cases (e q) <;> rfl

/-! ## K = 1 reduction -/

/-- `chain_xor [i]` is the single-mech XOR. -/
@[simp] theorem chain_xor_singleton (i : Fin 252) :
    chain_xor [i] = bb_xMech i := by
  unfold chain_xor
  exact ErrorVec_mul_identity_right (bb_xMech i)

/-- **No length-1 chain is a successful X-side attack.** -/
theorem bb_chain_attack_k1 :
    ∀ chain : List (Fin 252), chain.length = 1 →
      bb_chain_attack chain = false := by
  intro chain h
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp h
  unfold bb_chain_attack
  rw [chain_xor_singleton]
  -- bb_chain1XOR i = bb_xMech i (definitional)
  exact bb_chain_1_no_attack i

/-! ## K = 2 reduction -/

/-- `chain_xor [i, j] = ErrorVec.mul (bb_xMech i) (bb_xMech j)`. -/
@[simp] theorem chain_xor_pair (i j : Fin 252) :
    chain_xor [i, j] = ErrorVec.mul (bb_xMech i) (bb_xMech j) := by
  show ErrorVec.mul (bb_xMech i) (chain_xor [j]) = _
  rw [chain_xor_singleton]

/-- **No length-2 chain is a successful X-side attack.** -/
theorem bb_chain_attack_k2 :
    ∀ chain : List (Fin 252), chain.length = 2 →
      bb_chain_attack chain = false := by
  intro chain h
  -- Decompose `chain` into `[i, j]` using length = 2.
  match chain, h with
  | [i, j], _ =>
    unfold bb_chain_attack
    rw [chain_xor_pair]
    -- bb_chain2XOR i j = ErrorVec.mul (bb_xMech i) (bb_xMech j) (definitional)
    exact bb_chain_2_no_attack i j

/-! ## K = 3 reduction (uses the BV-ErrorVec bridge) -/

/-- `chain_xor [i, j, k] = bb_chain3XOR i j k`. -/
@[simp] theorem chain_xor_triple (i j k : Fin 252) :
    chain_xor [i, j, k] = bb_chain3XOR i j k := by
  show ErrorVec.mul (bb_xMech i) (chain_xor [j, k]) = _
  rw [chain_xor_pair]
  rfl

/-- **No length-3 chain is a successful X-side attack.**
    Discharged via the BV native_decide proof
    (`QStab.Paper.BB72BVBridge.bb_chain_3_no_attack`)
    plus the BV ↔ ErrorVec bridge. -/
theorem bb_chain_attack_k3 :
    ∀ chain : List (Fin 252), chain.length = 3 →
      bb_chain_attack chain = false := by
  intro chain h
  match chain, h with
  | [i, j, k], _ =>
    unfold bb_chain_attack
    rw [chain_xor_triple]
    exact QStab.Paper.BB72BVBridge.bb_chain_3_no_attack i j k

/-! ## K = 0 (empty chain) -/

/-- `chain_xor [] = identity 72`. -/
@[simp] theorem chain_xor_nil : chain_xor [] = ErrorVec.identity 72 := rfl

/-- **No empty chain is a successful X-side attack.**
    Trivial: identity ErrorVec has zero parity vs every stab and L_Z basis. -/
theorem bb_chain_attack_k0 :
    ∀ chain : List (Fin 252), chain.length = 0 →
      bb_chain_attack chain = false := by
  intro chain h
  rw [List.length_eq_zero_iff] at h
  subst h
  unfold bb_chain_attack
  rw [chain_xor_nil]
  unfold bb_isSuccess
  -- Both `.all` (true) and `.any` (false) reduce by parity_identity.
  simp [ErrorVec.parity_identity]

/-! ## Composite: K ≤ 3 fully discharged -/

/-- **No chain of length ≤ 3 is a successful X-side attack.**
    Combines K = 0, 1, 2, 3 cases. -/
theorem bb_chain_attack_le_3 :
    ∀ chain : List (Fin 252), chain.length ≤ 3 →
      bb_chain_attack chain = false := by
  intro chain h
  match hlen : chain.length with
  | 0 => exact bb_chain_attack_k0 chain hlen
  | 1 => exact bb_chain_attack_k1 chain hlen
  | 2 => exact bb_chain_attack_k2 chain hlen
  | 3 => exact bb_chain_attack_k3 chain hlen
  | n + 4 => omega

/-! ## Conditional composite: K ≤ 5 modulo K = 4, K = 5 chain bridges

The K = 4 and K = 5 chain-form theorems are not yet discharged in Lean.
Their CNF-form theorems (`bb72_k4_unsat`, `bb72_k5_unsat`) are proven in
`BB72k{4,5}SAT.lean`, but the bridge from CNF Unsat to chain attack
requires SAT-encoding-correctness work (see `notes/loop_status.md`).

Until then, the K ≤ 5 result is conditional on the chain-form K=4 and
K=5 hypotheses. Once the SAT-encoding bridge is built, those hypotheses
will be discharged and this theorem becomes unconditional.
-/

/-- **Conditional**: assuming K=4 and K=5 chain-form theorems, no chain of
    length ≤ 5 is a successful X-side attack. -/
theorem bb_chain_attack_le_5_of_k4_k5
    (h_k4 : ∀ chain : List (Fin 252), chain.length = 4 →
              bb_chain_attack chain = false)
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
  | 4 => exact h_k4 chain hlen
  | 5 => exact h_k5 chain hlen
  | n + 6 => omega

end QStab.Paper.BB72ChainAttack
