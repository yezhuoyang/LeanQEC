import QStab.Simulate

/-! # [[3,1,3]] Repetition code tests

The 3-qubit repetition code has:
- n = 3 physical qubits, k = 1 logical qubit, d = 3
- 2 stabilizer generators: Z₁Z₂ and Z₂Z₃
- We test with R = 3 rounds of measurement (6 total measurements)

These tests verify that the QStab semantic rules produce correct
syndrome measurements, inconsistency detection, and error counting.
-/

namespace QStab.Examples

open QECParams

/-! ## Code definition -/

/-- Stabilizer generators for the [[3,1,3]] repetition code.
    Stabilizer 0: Z₁Z₂ = [Z, Z, I]
    Stabilizer 1: Z₂Z₃ = [I, Z, Z] -/
def repStabilizers : Fin 2 → ErrorVec 3
  | ⟨0, _⟩ => fun | ⟨0, _⟩ => Pauli.Z | ⟨1, _⟩ => Pauli.Z | ⟨2, _⟩ => Pauli.I
  | ⟨1, _⟩ => fun | ⟨0, _⟩ => Pauli.I | ⟨1, _⟩ => Pauli.Z | ⟨2, _⟩ => Pauli.Z

/-- The [[3,1,3]] repetition code with 3 rounds of measurement. -/
def repCode3 : QECParams where
  n := 3
  k := 1
  d := 3
  R := 3
  numStab := 2
  stabilizers := repStabilizers
  r := 1
  C_budget := 1
  hn := by omega
  hns := by omega
  hR := by omega

-- Helper: Fin indices for numStab = 2
abbrev stab0 : Fin repCode3.numStab := ⟨0, by decide⟩
abbrev stab1 : Fin repCode3.numStab := ⟨1, by decide⟩

-- Helper: Fin indices for n = 3
abbrev q0 : Fin repCode3.n := ⟨0, by decide⟩
abbrev q1 : Fin repCode3.n := ⟨1, by decide⟩
abbrev q2 : Fin repCode3.n := ⟨2, by decide⟩

/-! ## Test 1: No errors — all measurements should see parity 0 -/

def s0 : State repCode3 := State.init repCode3

def s_noerr : State repCode3 :=
  runAllMeasurements repCode3 s0 10

#eval! showState repCode3 s_noerr

#eval! s_noerr.I_syn stab0   -- expected: false
#eval! s_noerr.I_syn stab1   -- expected: false
#eval! s_noerr.RI              -- expected: 0
#eval! s_noerr.lam_E           -- expected: 0

/-! ## Test 2: Single X₁ error — triggers stabilizer 0 only

X on qubit 0 anticommutes with Z₁Z₂ but commutes with Z₂Z₃. -/

def s_x1 : State repCode3 :=
  let s1 := applyType0 s0 q0 .X
  runAllMeasurements repCode3 s1 10

#eval! showState repCode3 s_x1

#eval! s_x1.I_syn stab0   -- expected: true  (X₁ anticommutes with Z₁Z₂)
#eval! s_x1.I_syn stab1   -- expected: false (X₁ commutes with Z₂Z₃)
#eval! s_x1.lam_E          -- expected: 1
#eval! s_x1.cnt0            -- expected: 1

/-! ## Test 3: Single X₂ error — triggers both stabilizers

X on qubit 1 anticommutes with both Z₁Z₂ and Z₂Z₃. -/

def s_x2 : State repCode3 :=
  let s1 := applyType0 s0 q1 .X
  runAllMeasurements repCode3 s1 10

#eval! showState repCode3 s_x2

#eval! s_x2.I_syn stab0   -- expected: true
#eval! s_x2.I_syn stab1   -- expected: true
#eval! s_x2.lam_E          -- expected: 1

/-! ## Test 4: Single X₃ error — triggers stabilizer 1 only

X on qubit 2 commutes with Z₁Z₂ but anticommutes with Z₂Z₃. -/

def s_x3 : State repCode3 :=
  let s1 := applyType0 s0 q2 .X
  runAllMeasurements repCode3 s1 10

#eval! showState repCode3 s_x3

#eval! s_x3.I_syn stab0   -- expected: false
#eval! s_x3.I_syn stab1   -- expected: true

/-! ## Test 5: Z error commutes with Z stabilizers — undetectable

Z on any qubit commutes with both Z₁Z₂ and Z₂Z₃. -/

def s_z1 : State repCode3 :=
  let s1 := applyType0 s0 q0 .Z
  runAllMeasurements repCode3 s1 10

#eval! showState repCode3 s_z1

#eval! s_z1.I_syn stab0   -- expected: false (Z commutes with Z)
#eval! s_z1.I_syn stab1   -- expected: false
#eval! s_z1.lam_E          -- expected: 1 (error injected, just undetected)

/-! ## Test 6: Type-III measurement bit flip — inconsistency detection -/

def s_flip : State repCode3 :=
  let s1 := applyType3 s0
  runAllMeasurements repCode3 s1 10

#eval! showState repCode3 s_flip

#eval! s_flip.RI  -- expected: > 0

/-! ## Test 7: Error counting invariant

totalErrors should equal C_budget - C after any execution. -/

#eval! s_noerr.totalErrors == repCode3.C_budget - s_noerr.C  -- expected: true
#eval! s_x1.totalErrors == repCode3.C_budget - s_x1.C        -- expected: true
#eval! s_x2.totalErrors == repCode3.C_budget - s_x2.C        -- expected: true
#eval! s_flip.totalErrors == repCode3.C_budget - s_flip.C     -- expected: true

end QStab.Examples
