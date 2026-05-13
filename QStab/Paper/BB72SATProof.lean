import Mathlib.Tactic.Sat.FromLRAT

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# BB72 NZ static-DEM check via SAT proof certificate (Path 1 / LeanSAT)

## Summary of what works end-to-end

  * **External SAT verification**: `cadical` returns UNSAT in 109s on
    `notes/bb72_static_dem.cnf` (10,169 clauses, 3,343 variables) for
    the full k ≤ 5 check.
  * **DRAT proof certificate**: cadical produces a 1.4M-line ASCII
    DRAT proof (`notes/bb72_static_dem.cadical_ascii.drat`).
  * **`drat-trim` verifies and converts to LRAT**: the LRAT proof has
    980,051 lemmas in core, uses 200M resolution steps, and the
    drat-trim certificate verifies in 167s.
  * **Mathlib's `lrat_proof` command**: imports LRAT certificates and
    produces Lean theorems. Verified to work on minimal examples in
    this file.

## Lean kernel limitation

The full k=5 LRAT proof (~1.5 GB, 1.5M lines) and even the k=2 LRAT
proof (3.4 MB, 13k lines) exceed the **Lean kernel's hardcoded
recursion depth**. The `set_option maxRecDepth` setting controls only
the elaborator, not the kernel.

This is a technology limitation of the current `lrat_proof` macro,
not of the SAT-based approach itself. Workarounds (any of):

  1. **Decompose the LRAT into smaller chunks** (each fitting under
     kernel recursion limit), prove sub-lemmas, then combine.
  2. **Use a streaming/iterative LRAT verifier** that doesn't build
     a deep recursive proof term.
  3. **Use Lean's `bv_decide` tactic** (Mathlib's bit-vector
     decision procedure), which calls SAT internally and bypasses
     kernel recursion via reflection.

## Status of Path 1 in this file

  * `bb72_pipeline_test` (below): minimal Mathlib docs example,
    confirms `lrat_proof` works in our setup. ✅
  * `bb72_k2_unsat` (commented out): would import the BB72 k=2 LRAT.
    Fails with "kernel deep recursion detected" — engineering blocker.
-/

/-! ## Tiny example to validate the `lrat_proof` pipeline

Minimal example from Mathlib docs: `(¬a ∧ ¬b) ∨ (a ∧ ¬b) ∨ (¬a ∧ b) ∨ (a ∧ b)`.
-/

lrat_proof bb72_pipeline_test
  "p cnf 2 4  1 2 0  -1 2 0  1 -2 0  -1 -2 0"
  "5 -2 0 4 3 0  5 d 3 4 0  6 1 0 5 1 0  6 d 1 0  7 0 5 2 6 0"

/-! ## Attempted import of full BB72 k=2 LRAT proof

The BB72 k=2 static-DEM SAT formula is UNSAT (verified externally
by CaDiCaL + drat-trim). The LRAT proof is in `bb72_k2.lrat`
(13,212 lines, 3.4 MB).

**Status: the Lean KERNEL hits its hardcoded recursion limit when
verifying this LRAT.** The `set_option maxRecDepth` setting controls
the elaborator, but the kernel's recursion limit is a separate
hardcoded value (~512 deep) that cannot be increased via options.

For the LRAT proof: 13k lines → proof term with ~13k nested resolution
applications → kernel rejects.

To make this work in practice would require:
  * **Decomposition**: split the LRAT into multiple smaller proofs,
    each fitting under the kernel limit, then combine.
  * **Native LRAT verifier**: write a Lean function that checks LRAT
    iteratively (using `IO` / `unsafe` for performance), bypassing the
    kernel's recursive proof-term construction.
  * **`bv_decide`-style approach**: encode the static-DEM check as a
    `BitVec` goal and let Mathlib's bit-vector tactics handle the
    kernel-friendly translation internally.

These are engineering paths that require more infrastructure than is
available in this session.
-/

-- Uncomment the following to attempt the actual import (will fail with
-- "kernel deep recursion detected"):
--
-- lrat_proof bb72_k2_unsat
--   (include_str "bb72_k2.cnf")
--   (include_str "bb72_k2.lrat")
