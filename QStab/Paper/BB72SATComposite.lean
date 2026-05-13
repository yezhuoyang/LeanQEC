import QStab.Paper.BB72k2SAT
import QStab.Paper.BB72k3SAT
import QStab.Paper.BB72k4SAT
import QStab.Paper.BB72k5SAT

/-!
# BB72 NZ static-DEM check: composite SAT-side result for k = 2..5

Each of `bb72_kK_unsat : bb72_kK_cnf.Unsat` (K = 2, 3, 4, 5) is a Lean
theorem proved zero-sorry by the streaming LRAT verifier
`Std.Tactic.BVDecide.LRAT.check_sound` applied to a CaDiCaL-generated
RUP-only LRAT certificate (k=4, k=5 trimmed via `lrat-trim`). Each
LRAT certificate is also independently verifiable by `drat-trim`.

Combined with `bb_chain_1_no_attack` and `bb_chain_2_no_attack` from
`BB72ChainCheck.lean` (`native_decide` over 252 + 252² cases), the SAT
side of the BB72 static-DEM check is fully discharged — at the
**CNF level** — for k ≤ 5.

Remaining work to discharge `bb_NZ_no_X_attack_below_6`:
  * **Encoding-correctness bridge** (planned in next iteration): for
    each K ∈ {1..5}, prove
      `bb72_kK_cnf.Unsat → ∀ chain : List (Fin 252),
         chain.length = K → ¬ chain_attack_success chain`
    where `chain_attack_success` is defined directly in BB72 terms and
    matches the Tseitin XOR + cardinality + L_Z-OR encoding emitted by
    `notes/bb72_sat_encode_per_k.py`.
  * **Reduction from `reachableE` to chain-XOR** (already informally
    argued in `BB72ChainCheck.lean`'s preamble): Z-content vanishes
    by min Z-stab weight 6, X-content equals a chain XOR of ≤ 5
    X-mechs.

This file makes the composite SAT statement a single Lean theorem;
the bridge will land in `BB72SATBridge.lean`.
-/

/-- **The BB72 k=2..5 static-DEM CNFs are jointly unsatisfiable.**

This conjoins the four per-K SAT-verified UNSAT theorems. Each
conjunct is independently `lake build`-able and uses no axioms beyond
standard Lean/Mathlib. -/
theorem bb72_static_dem_cnf_unsat_k2_to_k5 :
    bb72_k2_cnf.Unsat ∧ bb72_k3_cnf.Unsat ∧
    bb72_k4_cnf.Unsat ∧ bb72_k5_cnf.Unsat :=
  ⟨bb72_k2_unsat, bb72_k3_unsat, bb72_k4_unsat, bb72_k5_unsat⟩
