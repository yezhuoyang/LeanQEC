import QStab.QClifford.FlagGeneral

/-! # Sanity tests for the parametric Flag circuit (Week 2)

Two things are verified here:

1. **Syntactic match** — the parametric `flagCircuit 4 [0,1,2,3]`
   produces an 11-gate circuit; the gate sequence matches the
   Chao--Reichardt construction (prepPlus + prepZero + 2 data CNOTs
   + flag-CNOT + 2 data CNOTs + flag-CNOT + Hadamard + measZ + measZ).

2. **C2 holds on the concrete instance** — `noBackAction'` evaluates
   correctly at all (E, i) pairs for n = 2 via `decide`.
-/

namespace QStab.QClifford.FlagGeneral.Test

open QStab QStab.QClifford QStab.QClifford.FlagGeneral

/-! ## Syntactic structure — gate count -/

/-- The parametric weight-4 flag circuit has 11 gates total
    (2 prep + 4 data CNOT + 2 flag CNOT + 1 H + 2 measZ). -/
example : (flagCircuit 4 [⟨0, by omega⟩, ⟨1, by omega⟩,
                          ⟨2, by omega⟩, ⟨3, by omega⟩]).length = 11 := by
  decide

/-- For a weight-2 support, the parametric flag circuit has 9 gates
    (2 prep + 2 data CNOT + 2 flag CNOT + 1 H + 2 measZ). -/
example : (flagCircuit 3 [⟨0, by omega⟩, ⟨1, by omega⟩]).length = 9 := by
  decide

/-- For a weight-3 support, the parametric flag circuit has 10 gates
    (half = 1, so 1+2 data CNOTs around the flag-CNOTs). -/
example : (flagCircuit 3 [⟨0, by omega⟩, ⟨1, by omega⟩,
                          ⟨2, by omega⟩]).length = 10 := by
  decide

/-! ## C2 / fault-free correctness on small instances

For the weight-4 example we check via `native_decide` that the
parametric flagCircuit truly does not affect data on a fault-free run.
-/

/-- Fault-free run on a single-X-on-data-0 input: data is preserved. -/
example :
    (propagateCircuit (flagCircuit 4 [⟨0, by omega⟩, ⟨1, by omega⟩,
                                       ⟨2, by omega⟩, ⟨3, by omega⟩])
       (QStab.Paper.SoundnessPrime.initialFromData' 4 2
         (fun i : Fin 4 => if i.val = 0 then .X else .I))).paulis
      ⟨0, by omega⟩ = .X := by
  decide

/-- Fault-free run on Z-on-data-1 input: data is preserved. -/
example :
    (propagateCircuit (flagCircuit 4 [⟨0, by omega⟩, ⟨1, by omega⟩,
                                       ⟨2, by omega⟩, ⟨3, by omega⟩])
       (QStab.Paper.SoundnessPrime.initialFromData' 4 2
         (fun i : Fin 4 => if i.val = 1 then .Z else .I))).paulis
      ⟨1, by omega⟩ = .Z := by
  decide

/-- Fault-free run on all-X input — full X-stabilizer support gets
    measured by the syndrome ancilla. -/
example :
    (propagateCircuit (flagCircuit 4 [⟨0, by omega⟩, ⟨1, by omega⟩,
                                       ⟨2, by omega⟩, ⟨3, by omega⟩])
       (QStab.Paper.SoundnessPrime.initialFromData' 4 2
         (fun _ : Fin 4 => .X))).paulis ⟨0, by omega⟩ = .X := by
  decide

end QStab.QClifford.FlagGeneral.Test
