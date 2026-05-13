import QStab.Paper.BB72Instance
import Mathlib.Tactic.FinCases

/-!
# BB72 NZ X-side static-DEM check: small-k discharged in Lean

The X-side axiom in `BB72Instance` reads
```
axiom bb_NZ_no_X_attack_below_6 :
    ∀ E ∈ reachableE bb_allHooks 5, bb_isSuccess E = false
```
which expresses "no element of the X-side reachable set at depth 5 is a
successful attack". The intractable part is the union over k=1..5
chains; the dominant term is k=5 (~10¹⁰ chains, Python MITM ~5 min).

This file shrinks the trust boundary by **discharging k=1 and k=2
directly in Lean** via `native_decide`. The chain-XOR formulation is
the *static-DEM check*: no chain of `k` distinct mechs (Type-0 X +
X-hooks) yields a chain XOR that is a successful X-side attack.

## What is discharged in Lean and what remains external

| k | # chains | Status | Wall-clock |
|---|---|---|---|
| 1 | 252 | ✅ `native_decide` | trivial |
| 2 | 63,504 | ✅ `native_decide` | ~15 min |
| 3 | 2.6 M | 🌐 axiom (Python MITM) | infeasible in `native_decide` (~66 h) |
| 4 | 165 M | 🌐 axiom (Python MITM) | infeasible |
| 5 | 8.1 G | 🌐 axiom (Python MITM) | infeasible without HashMap |

The Lean `native_decide` backend at this encoding (Finset-based parity)
is dominated by per-case parity recomputation and does not scale past
k=2. To push further would require a bit-packed ErrorVec
representation and a SAT/DRAT pipeline; left as future work.

## Bridge from `reachableE` to chain-XOR

`reachableE bb_allHooks 5` contains all `E_tilde` reachable in ≤5
elementary steps (single-qubit updates with any `p ≠ I`, or
multiplications by hooks from `bb_allHooks`). For `bb_isSuccess`:

  * Z-content commutes with all 36 X-stabs ⟹ Z-content lies in
    ker(X-stab); for ≤5 Type-0 Z mechs, by min Z-stab weight = 6,
    Z-content must vanish.
  * X-content equals a chain XOR of ≤5 X-mechs (Type-0 X + X-hook).
  * "Some L_Z basis parity 1" decomposes through X-content (L_Z is
    Z-only).

So the X-side axiom on `reachableE` reduces to: no chain XOR of ≤5
X-mechs is a successful attack. This file's `bb_chain_1_no_attack`
and `bb_chain_2_no_attack` discharge that for k=1, 2 unconditionally.
-/

namespace QStab.Paper.BB72ChainCheck

open QStab QStab.Paper.BB72Instance

/-! ## Unified X-mech indexing: 252 mechs (72 Type-0 X + 180 X-hooks) -/

/-- Index `i : Fin 252`:
    * `i.val < 72`: Type-0 X mech at qubit `i.val`.
    * `i.val ≥ 72`: X-hook number `i.val - 72` from `bb_allHooks`. -/
def bb_xMech (i : Fin 252) : ErrorVec 72 :=
  if h : i.val < 72 then
    ErrorVec.update (ErrorVec.identity 72) ⟨i.val, by omega⟩ .X
  else
    bb_allHooks.getD (i.val - 72) (ErrorVec.identity 72)

/-! ## Chain-XOR: combine `k` mechs by ErrorVec.mul -/

/-- 1-mech chain XOR is just the mech itself. -/
@[simp] def bb_chain1XOR (i : Fin 252) : ErrorVec 72 := bb_xMech i

/-- 2-mech chain XOR. -/
@[simp] def bb_chain2XOR (i j : Fin 252) : ErrorVec 72 :=
  ErrorVec.mul (bb_xMech i) (bb_xMech j)

/-- 3-mech chain XOR. -/
@[simp] def bb_chain3XOR (i j k : Fin 252) : ErrorVec 72 :=
  ErrorVec.mul (bb_xMech i) (ErrorVec.mul (bb_xMech j) (bb_xMech k))

/-! ## Static-DEM check at k=1: discharged in Lean -/

/-- **No single mech is a successful X-side attack.**
    Verified by `native_decide` over 252 cases. -/
theorem bb_chain_1_no_attack :
    ∀ i : Fin 252, bb_isSuccess (bb_chain1XOR i) = false := by
  native_decide

/-! ## Static-DEM check at k=2: discharged in Lean -/

/-- **No 2-mech chain is a successful X-side attack.**
    Verified by `native_decide` over 252² = 63,504 ordered pairs. -/
theorem bb_chain_2_no_attack :
    ∀ i j : Fin 252, bb_isSuccess (bb_chain2XOR i j) = false := by
  native_decide

end QStab.Paper.BB72ChainCheck
