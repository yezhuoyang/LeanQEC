import QStab.Examples.HGPCode
import QStab.Examples.SurfaceGeneral

/-! # Smoke test: [[13,1,3]] as an `HGPSpec 3` under the new `Option`-valued partition

This file is a **type-level smoke test** for the refactored `HGPSpec`
signature (`col : Fin params.n → Option (Fin d)`).  It assembles a
partial `HGPSpec 3` for the `HGP13` code defined in `HGPCode.lean`.

Sector 1 (qubits 0-8) is partitioned by column:
  column 0 = {0, 3, 6}, column 1 = {1, 4, 7}, column 2 = {2, 5, 8}.
Sector 2 ancillas (qubits 9-12) are mapped to `none`.

The combinatorial field `hook_in_column` is discharged **vacuously**
because `HGP13.backActionSet = fun _ => ∅` in the present `HGP13.code`
definition (see `HGPCode.lean`).  No `sorry` is needed at this phase.

The next workflow will replace the empty `backActionSet` with a real
hook set and discharge `hook_in_column` non-vacuously.
-/

namespace QStab.Examples.HGP13Smoketest

open QStab QStab.Examples QStab.Examples.HGP13 QStab.Examples.SurfaceGeneral

/-! ## Column partition restricted to S1, `none` for S2 ancillas

`col q = some (q.val % 3)` for `q ∈ {0,...,8}` (Sector 1),
`col q = none` for `q ∈ {9,10,11,12}` (Sector 2 ancillas). -/

def hgp13Col : Fin 13 → Option (Fin 3)
  | ⟨0, _⟩  => some 0 | ⟨1, _⟩  => some 1 | ⟨2, _⟩  => some 2   -- S1 row 0
  | ⟨3, _⟩  => some 0 | ⟨4, _⟩  => some 1 | ⟨5, _⟩  => some 2   -- S1 row 1
  | ⟨6, _⟩  => some 0 | ⟨7, _⟩  => some 1 | ⟨8, _⟩  => some 2   -- S1 row 2
  | ⟨9, _⟩  => none   | ⟨10, _⟩ => none                          -- S2 ancillas
  | ⟨11, _⟩ => none   | ⟨12, _⟩ => none

/-! ## `cutOp_spec` for the S1-only partition

Each `cutOp i` is `Z` on column `i` of S1 and `I` everywhere else
(including all S2 ancillas).  Concretely:

* `cutOp 0 = Z` on `{0, 3, 6}`, `I` on `{1,2,4,5,7,8}` (other S1 cols)
  and on `{9,10,11,12}` (S2 ancillas).
* `cutOp 1 = Z` on `{1, 4, 7}`, `I` elsewhere.
* `cutOp 2 = Z` on `{2, 5, 8}`, `I` elsewhere.

The matching `if hgp13Col q = some i then .Z else .I` reduces by `decide`. -/

theorem hgp13_cutOp_spec :
    ∀ (i : Fin 3) (q : Fin 13),
      HGP13.cutOp i q = if hgp13Col q = some i then .Z else .I := by
  decide

/-! ## The partial `HGPSpec 3` instance

All fields are populated from existing `HGP13.*` declarations.
Because `HGP13.backActionSet = fun _ => ∅`, the `hook_in_column`
field is discharged vacuously by `fun _ _ h => h.elim` — **no
`sorry` is used in this file**. -/

def hgp13Spec_partial : HGPSpec 3 where
  params := HGP13.code
  hd_pos := by decide
  logicalZ := HGP13.logicalZ
  col := hgp13Col
  cutOp := HGP13.cutOp
  cutOp_stabEquiv := fun i => by
    match i with
    | ⟨0, _⟩ =>
        -- cutOp 0 = logicalZ = I · logicalZ.
        refine ⟨ErrorVec.identity 13, InStab.identity, ?_⟩
        rw [HGP13.cut0_eq_logicalZ]; exact (ErrorVec.mul_identity_left _).symm
    | ⟨1, _⟩ => exact HGP13.cut01_stabilizer_equiv
    | ⟨2, _⟩ => exact HGP13.cut02_stabilizer_equiv
  cutOp_spec := hgp13_cutOp_spec
  logicalZ_normalizer := HGP13.logicalZ_normalizer
  stab_commute := HGP13.stab_commute
  -- `HGP13.backActionSet = fun _ => ∅`, so `e_B ∈ ∅` is uninhabited:
  -- the entire field is discharged vacuously, no `sorry` required.
  hook_in_column := fun _ _ h => h.elim

/-! ## Type-level smoke test

`#check (hgp13Spec_partial : HGPSpec 3)` typechecks: the refactored
framework accepts `[[13,1,3]]` at the type level.  The `col` field
matches the new `Fin params.n → Option (Fin 3)` signature, and all
other fields are discharged by existing `HGPCode.lean` proofs. -/

#check (hgp13Spec_partial : HGPSpec 3)

/-- The headline `hgp_distance_ge_d` specialized to `hgp13Spec_partial`. -/
theorem hgp13_distance_ge_d
    (s : State hgp13Spec_partial.params)
    (hreach : MultiStep hgp13Spec_partial.params
                  (.active (State.init hgp13Spec_partial.params)) (.active s))
    (hSyn : ∀ i : Fin hgp13Spec_partial.params.numStab,
             ErrorVec.parity (hgp13Spec_partial.params.stabilizers i) s.E_tilde = false)
    (hLog : ErrorVec.parity hgp13Spec_partial.logicalZ s.E_tilde = true) :
    hgp13Spec_partial.params.C_budget - s.C ≥ 3 :=
  hgp_distance_ge_d hgp13Spec_partial s hreach hSyn hLog

end QStab.Examples.HGP13Smoketest
