import QStab.Compiler.ToCircuit
import QStab.Examples.CompilerTest

/-! # Smoke tests for the QStab→QClifford circuit translator

Confirms `toCircuitXRound` / `toCircuitX` produce non-empty circuits
from the Surface d=3 `CodeSpec`. The numbers are unit checks;
correctness (SchemeCorrect, qstab_sound) is established separately.

Surface d=3 (NZ scheduling, 8 stabilizers, 4 bulk weight-4 + 4
boundary weight-2):
- X-stabilizer gadget: `|gateOrdering s| + 3` gates.
- Z-stabilizer gadget: `|gateOrdering s| + 2` gates.

Per `surfaceD3Spec.gateOrdering`:
- s=0: 4 → X-side 7, Z-side 6
- s=4: 2 → X-side 5, Z-side 4
- etc.

Uses the length lemmas plus arithmetic to confirm gate counts without
running full `decide` on the gate list (which exceeds `maxRecDepth`). -/

namespace QStab.Compiler.ToCircuitTest

open QStab.Compiler QStab.Examples.CompilerTest

/-- Stabilizer 0 (bulk Z, weight 4) X-side gadget has 7 gates. -/
example : (toCircuitStabilizerX surfaceD3Spec ⟨0, by decide⟩).length = 7 := by
  rw [toCircuitStabilizerX_length]; decide

/-- Stabilizer 4 (boundary X, weight 2) X-side gadget has 5 gates. -/
example : (toCircuitStabilizerX surfaceD3Spec ⟨4, by decide⟩).length = 5 := by
  rw [toCircuitStabilizerX_length]; decide

/-- Stabilizer 0 Z-side gadget has 6 gates. -/
example : (toCircuitStabilizerZ surfaceD3Spec ⟨0, by decide⟩).length = 6 := by
  rw [toCircuitStabilizerZ_length]; decide

/-- The X-round has the expected total length 48 = 4*7 + 4*5. -/
example : (toCircuitXRound surfaceD3Spec).length = 48 := by
  rw [toCircuitXRound_length]; decide

/-- The Z-round has the expected total length 40 = 4*6 + 4*4. -/
example : (toCircuitZRound surfaceD3Spec).length = 40 := by
  rw [toCircuitZRound_length]; decide

/-- The compiled X-circuit (R=3 rounds) is non-empty. Uses the length
    lemma to avoid expanding the full 144-gate list. -/
example : (toCircuitX surfaceD3Spec).length > 0 := by
  rw [toCircuitX_length]
  decide

/-- Z-circuit also non-empty. -/
example : (toCircuitZ surfaceD3Spec).length > 0 := by
  rw [toCircuitZ_length]
  decide

end QStab.Compiler.ToCircuitTest
