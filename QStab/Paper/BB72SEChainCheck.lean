import QStab.Paper.BB72SEInstance

/-!
# BB72 SE static-DEM chain checks (k=1 and k=2)

Discharged in Lean via `native_decide`, unconditional.

This file is split out from `BB72SEInstance.lean` because the k=2
`native_decide` over 63,504 cases takes ~15 minutes to compile —
isolating it here keeps the main instance file fast to iterate on.

## What's discharged

  * `bb_se_chain_1_no_attack`: no single SE mech is an X-side attack
    (252 cases, ~1 sec).
  * `bb_se_chain_2_no_attack`: no 2-mech SE chain is an X-side attack
    (252² = 63,504 ordered pairs, ~15 min).

## Trust-boundary contribution

These theorems do NOT replace `bb_NZ_SE_no_X_attack_below_6` (the
combined axiom in `BB72SEInstance.lean`); they sit alongside it as
independent Lean-checked verification of k=1 and k=2.

A future structural lemma `reachableE_to_chainXOR_reduction` will
formally split the combined axiom into per-k pieces, at which point
the k=1, 2 axioms can be REPLACED by these theorems. That bridge is
left as future work.

For SE the orbit-reduction lemma (sketched in `BB72SEInstance.lean`'s
"Open path") would make k=2 trivial (~880 orbit-pairs ⇒ <1 sec
`native_decide`). Implementing it requires the structural
shift-invariance lemmas already in place in `BB72SEInstance.lean`.
-/

namespace QStab.Paper.BB72SEChainCheck

open QStab QStab.Paper.BB72SEInstance

/-- **No single SE mech is a successful X-side attack.** Verified by
    `native_decide` over 252 cases. Unconditional. -/
theorem bb_se_chain_1_no_attack :
    ∀ i : Fin 252, bb_se_isSuccess (bb_se_xMech i) = false := by
  native_decide

/-- **No 2-mech SE chain is a successful X-side attack.** Verified by
    `native_decide` over 252² = 63,504 ordered pairs. Unconditional. -/
theorem bb_se_chain_2_no_attack :
    ∀ i j : Fin 252,
      bb_se_isSuccess (ErrorVec.mul (bb_se_xMech i) (bb_se_xMech j)) = false := by
  native_decide

end QStab.Paper.BB72SEChainCheck
