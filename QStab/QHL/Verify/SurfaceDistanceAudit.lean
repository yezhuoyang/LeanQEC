import QStab.QHL.Verify.SurfaceDistanceProver
import Lean

/-!
# Surface-code distance — verification audit (immutable)

This file is part of the trusted boundary; the prover must not edit it.  Building
this module is the single pass/fail gate for the whole effort:

* it **fails to build** (hard error) while the proof is incomplete or cheated,
* it **builds** exactly when `surface_code_has_distance_d_for_all_odd_d` is a
  genuine, axiom-clean, `∀ d` theorem.

## The gate: `#assert_clean_axioms`

`collectAxioms` gathers the *complete transitive* axiom dependency of a constant.
We reject anything outside the standard benign set
`{propext, Classical.choice, Quot.sound}`.  This catches, with no false
negatives:

* `sorryAx`           — any remaining `sorry`/`admit`/unfinished proof;
* `Lean.ofReduceBool` — any `native_decide` (the only `decide`-family escape that
  trusts the compiler);
* any `axiom`         — a prover-introduced shortcut primitive.

Because the audited theorem is a `∀ D` `Prop` produced through the contract's
`accept` (which routes only through kernel soundness), there is no way to satisfy
it with `#eval`/`decide`-at-concrete-d either: those never produce the `Prop`.
-/

open Lean Elab Command in
/-- `#assert_clean_axioms Fully.Qualified.name` errors unless the named constant
depends only on the benign axioms `{propext, Classical.choice, Quot.sound}`. -/
elab "#assert_clean_axioms " id:ident : command => do
  let name := id.getId
  unless (← getEnv).contains name do
    throwError "#assert_clean_axioms: unknown constant '{name}'"
  let axs ← liftCoreM <| Lean.collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := axs.filter (fun a => !(allowed.contains a))
  unless bad.isEmpty do
    throwError m!"❌ CHEAT DETECTED: '{name}' depends on forbidden axioms {bad.toList}.\n\
      Allowed: {allowed}.\n\
      (sorryAx = sorry/admit/unproved obligation; Lean.ofReduceBool = native_decide; \
      anything else = a prover-introduced axiom.)"
  logInfo m!"✅ axiom-clean: '{name}' depends only on {axs.toList}"

/-! ## Primary gate.

`audited_surface_distance` pins **the exact statement**: it must inhabit
`∀ D, SurfaceDistanceSpec D` where `SurfaceDistanceSpec` lives in the immutable
contract, so the prover cannot silently weaken the goal (e.g. to `∀ D, True`).
The `#assert_clean_axioms` below then pins **the proof discipline**: no `sorry`,
no `native_decide`, no custom axiom.  Both must hold for this module to build. -/

-- Positive check: the contract's reduction `accept` is itself axiom-clean, so
-- the *only* obstacle to a green build is the prover's witness obligations.
#assert_clean_axioms QHL.CodeLang.Surface.Verify.accept

theorem audited_surface_distance :
    ∀ (D : QHL.CodeLang.Surface.OddSurfaceDistance),
      QHL.CodeLang.Surface.Verify.SurfaceDistanceSpec D :=
  QHL.CodeLang.Surface.Verify.Prover.surface_code_has_distance_d_for_all_odd_d

#print axioms audited_surface_distance

-- HARD FAILURE while any obligation is `sorry`/cheated; passes only when the
-- `∀ d` proof is genuinely complete and axiom-clean.
#assert_clean_axioms audited_surface_distance

/-! ## Secondary anti-tamper canaries.

These confirm the recursive AST `code.body` and the formula builders the spec
refers to still denote the genuine Surface code (a valid distance-3 and -5 code).
They are *not* the proof — the proof is the `∀ d` theorem above — but they detect
silent weakening of the object being verified.  (Fast compiled `#eval`, asserted
via `#guard_msgs`.) -/

section AntiTamper
open QHL.CodeLang.Surface

/-- info: true -/
#guard_msgs in
#eval surfaceCodeLevelChecked OddSurfaceDistance.d3

/-- info: true -/
#guard_msgs in
#eval surfaceCodeLevelChecked OddSurfaceDistance.d5

/-- info: true -/
#guard_msgs in
#eval surfaceCodeDistanceFamilyCheckedAtGenericCuts OddSurfaceDistance.d3

/-- info: true -/
#guard_msgs in
#eval surfaceCodeDistanceFamilyCheckedAtGenericCuts OddSurfaceDistance.d5

end AntiTamper
