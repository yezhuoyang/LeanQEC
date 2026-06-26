import QStab.QClifford.PCC.VCGen
import QStab.QClifford.Compile.Calculus
import QStab.QClifford.SurfaceD3Distance

/-!
# Surface-d3 client for the QClifford PCC kernel

This file packages the already kernel-checked QClifford surface-d3 geometry as
a `DistanceCertificate`, then obtains the public paper-style safety policy by
applying the generic PCC theorem `certificate_sound`.
-/

namespace QStab.QClifford.PCC.SurfaceD3

abbrev DataQ := QStab.Paper.SurfaceD3CircuitDistance.DataQ
abbrev DataPauli := QStab.Paper.SurfaceD3CircuitDistance.DataPauli
abbrev StabIdx := QStab.Paper.SurfaceD3CircuitDistance.StabIdx

def fq (n : Nat) (h : n < 10 := by decide) : Fin 10 := ⟨n, h⟩

def q9 : Fin 10 := QStab.QClifford.SurfaceD3Distance.qq 9

def flag8 (n : Nat) (h : n < 8 := by decide) : Fin 8 := ⟨n, h⟩

def stabSyntax (support : List (Fin 10 × Pauli)) : StabilizerSyntax 10 where
  support := support

def surfaceCodeSyntax : StabilizerCodeSyntax 10 where
  nq_pos := by decide
  dataQubits := [fq 0, fq 1, fq 2, fq 3, fq 4, fq 5, fq 6, fq 7, fq 8]
  stabilizers :=
    [ stabSyntax [(fq 0, .Z), (fq 1, .Z), (fq 3, .Z), (fq 4, .Z)]
    , stabSyntax [(fq 1, .X), (fq 2, .X), (fq 4, .X), (fq 5, .X)]
    , stabSyntax [(fq 3, .X), (fq 4, .X), (fq 6, .X), (fq 7, .X)]
    , stabSyntax [(fq 4, .Z), (fq 5, .Z), (fq 7, .Z), (fq 8, .Z)]
    , stabSyntax [(fq 0, .X), (fq 1, .X)]
    , stabSyntax [(fq 2, .Z), (fq 5, .Z)]
    , stabSyntax [(fq 3, .Z), (fq 6, .Z)]
    , stabSyntax [(fq 7, .X), (fq 8, .X)] ]
  numStab_pos := by decide
  numFlags := 8
  d := 3
  d_pos := by decide

def fullOfData (E : DataPauli) : Fin 10 -> Pauli :=
  fun q => if h : q.val < 9 then E ⟨q.val, h⟩ else Pauli.I

def surfaceStabilizer (i : StabIdx) : Fin 10 -> Pauli :=
  fullOfData (QStab.Paper.SurfaceD3CircuitDistance.stabAt i)

def surfaceGadget : StabIdx -> FCircuit 10
  | ⟨0, _⟩ => QStab.QClifford.SurfaceD3Distance.G0
  | ⟨1, _⟩ => QStab.QClifford.SurfaceD3Distance.G1
  | ⟨2, _⟩ => QStab.QClifford.SurfaceD3Distance.G2
  | ⟨3, _⟩ => QStab.QClifford.SurfaceD3Distance.G3
  | ⟨4, _⟩ => QStab.QClifford.SurfaceD3Distance.G4
  | ⟨5, _⟩ => QStab.QClifford.SurfaceD3Distance.G5
  | ⟨6, _⟩ => QStab.QClifford.SurfaceD3Distance.G6
  | _ => QStab.QClifford.SurfaceD3Distance.G7

def surfaceGadgetsSyntax : List (FCircuit 10) :=
  [ QStab.QClifford.SurfaceD3Distance.G0
  , QStab.QClifford.SurfaceD3Distance.G1
  , QStab.QClifford.SurfaceD3Distance.G2
  , QStab.QClifford.SurfaceD3Distance.G3
  , QStab.QClifford.SurfaceD3Distance.G4
  , QStab.QClifford.SurfaceD3Distance.G5
  , QStab.QClifford.SurfaceD3Distance.G6
  , QStab.QClifford.SurfaceD3Distance.G7 ]

def surfaceExtractionSyntax : ExtractionSyntax surfaceCodeSyntax where
  stabilizerReadouts :=
    [[flag8 0], [flag8 1], [flag8 2], [flag8 3],
     [flag8 4], [flag8 5], [flag8 6], [flag8 7]]
  stabilizerReadouts_length := by decide
  postselectFlags := []
  detectorStarts := [0, 1, 2, 3, 4, 5, 6, 7]
  detectorStarts_length := by decide
  gadgets := surfaceGadgetsSyntax
  gadgets_length := by decide
  expectedProgram := circuitView QStab.QClifford.SurfaceD3Distance.C_NZ_D3
  readout_disjoint := by decide

theorem surfaceCircuit_from_compile :
    QStab.QClifford.Compile.SurfaceD3.compiledCircuit =
      QStab.QClifford.SurfaceD3Distance.C_NZ_D3 :=
  QStab.QClifford.Compile.SurfaceD3.compiledCircuit_eq_C_NZ_D3

def surfaceSpec : CodeSpec 10 where
  numStab := 8
  numFlags := 8
  isData := fun q => decide (q.val < 9)
  stabilizer := surfaceStabilizer
  stabilizerReadout := fun i => [⟨i.val, i.isLt⟩]
  postselectFlag := fun _ => false
  flagSlot := fun i => i.val
  flagSlot_injective := by
    intro a b h
    exact Fin.ext h
  flagSlot_ordered := by
    intro i
    rfl
  readout_disjoint := by
    intro i j hij s hs_i hs_j
    simp only [List.mem_singleton] at hs_i hs_j
    apply hij
    apply Fin.ext
    calc
      i.val = s.val := by rw [hs_i]
      _ = j.val := by rw [hs_j]
  gadgetDetectorStart := fun i => i.val
  gadget := surfaceGadget
  expectedProgram := circuitView QStab.QClifford.SurfaceD3Distance.C_NZ_D3
  d := 3
  d_pos := by decide

def surfaceBarrierData (E : DataPauli) : Nat :=
  if QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR E 0 then 0
  else if QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR E 1 then 1
  else if QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR E 2 then 2
  else 3

def surfaceBarrier (es : ErrorState 10) : Nat :=
  surfaceBarrierData (QStab.QClifford.SurfaceD3Distance.dataPart es)

def surfaceD3SyntaxInput : VCInputSyntax 10 where
  program := QStab.QClifford.SurfaceD3Distance.C_NZ_D3
  code := surfaceCodeSyntax
  extraction := surfaceExtractionSyntax
  mode := .unconditional

abbrev surfaceD3GeneratedVCs : GeneratedVCs surfaceD3SyntaxInput.toVCInput :=
  vcgen surfaceD3SyntaxInput.toVCInput

abbrev surfaceSyntaxSpec : CodeSpec 10 :=
  surfaceD3SyntaxInput.toVCInput.toCodeSpec

example :
    surfaceD3GeneratedVCs.slots =
      [.programEq, .wf, .syn, .ftDistance, .reach] := rfl

example :
    surfaceD3GeneratedVCs.hoare =
      hoareSkeleton surfaceD3SyntaxInput.toVCInput := rfl

theorem dataVector_surface (es : ErrorState 10) :
    dataVector surfaceSpec es =
      fullOfData (QStab.QClifford.SurfaceD3Distance.dataPart es) := by
  funext q
  by_cases h : q.val < 9
  · simp [dataVector, surfaceSpec, fullOfData, QStab.QClifford.SurfaceD3Distance.dataPart,
      h]
  · simp [dataVector, surfaceSpec, fullOfData, h]

theorem anticommute_eq_paper (a b : Pauli) :
    anticommute a b = QStab.Paper.SurfaceD3CircuitDistance.anticommutes a b := by
  cases a <;> cases b <;> rfl

theorem vectorParity_fullOfData (S E : DataPauli) :
    vectorParity (fullOfData S) (fullOfData E) =
      QStab.Paper.SurfaceD3CircuitDistance.parity S E := by
  unfold vectorParity QStab.Paper.SurfaceD3CircuitDistance.parity fullOfData
  simp [List.finRange, anticommute_eq_paper, QStab.Paper.SurfaceD3CircuitDistance.anticommutes]

@[simp] theorem apply_fin10_0 (E : Fin 10 -> Pauli) (h : 0 < 10) :
    E (Fin.mk 0 h) = E (0 : Fin 10) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_fin10_1 (E : Fin 10 -> Pauli) (h : 1 < 10) :
    E (Fin.mk 1 h) = E (1 : Fin 10) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_fin10_2 (E : Fin 10 -> Pauli) (h : 2 < 10) :
    E (Fin.mk 2 h) = E (2 : Fin 10) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_fin10_3 (E : Fin 10 -> Pauli) (h : 3 < 10) :
    E (Fin.mk 3 h) = E (3 : Fin 10) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_fin10_4 (E : Fin 10 -> Pauli) (h : 4 < 10) :
    E (Fin.mk 4 h) = E (4 : Fin 10) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_fin10_5 (E : Fin 10 -> Pauli) (h : 5 < 10) :
    E (Fin.mk 5 h) = E (5 : Fin 10) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_fin10_6 (E : Fin 10 -> Pauli) (h : 6 < 10) :
    E (Fin.mk 6 h) = E (6 : Fin 10) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_fin10_7 (E : Fin 10 -> Pauli) (h : 7 < 10) :
    E (Fin.mk 7 h) = E (7 : Fin 10) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_fin10_8 (E : Fin 10 -> Pauli) (h : 8 < 10) :
    E (Fin.mk 8 h) = E (8 : Fin 10) := by
  exact congrArg E (Fin.ext rfl)

theorem vectorParity_surfaceStabilizer (i : StabIdx) (E : Fin 10 -> Pauli) :
    vectorParity (surfaceStabilizer i) E =
      QStab.Paper.SurfaceD3CircuitDistance.parity
        (QStab.Paper.SurfaceD3CircuitDistance.stabAt i)
        (fun d => E (QStab.QClifford.SurfaceD3Distance.physOfData d)) := by
  rw [← vectorParity_fullOfData
    (QStab.Paper.SurfaceD3CircuitDistance.stabAt i)
    (fun d => E (QStab.QClifford.SurfaceD3Distance.physOfData d))]
  unfold vectorParity surfaceStabilizer fullOfData
  simp [List.finRange, QStab.QClifford.SurfaceD3Distance.physOfData, anticommute]

@[simp] theorem hasXComp_pauliMul (a b : Pauli) :
    hasXComp (pauliMul a b) = (hasXComp a ^^ hasXComp b) := by
  cases a <;> cases b <;> rfl

@[simp] theorem hasZComp_pauliMul (a b : Pauli) :
    hasZComp (pauliMul a b) = (hasZComp a ^^ hasZComp b) := by
  cases a <;> cases b <;> rfl

@[simp] theorem hasXComp_xPart_eq_anticommute_Z (p : Pauli) :
    hasXComp (xPart p) = anticommute Pauli.Z p := by
  cases p <;> rfl

@[simp] theorem hasZComp_zPart_eq_anticommute_X (p : Pauli) :
    hasZComp (zPart p) = anticommute Pauli.X p := by
  cases p <;> rfl

@[simp] theorem hasXComp_hadamardAction_eq_hasZComp (p : Pauli) :
    hasXComp (hadamardAction p) = hasZComp p := by
  cases p <;> rfl

theorem xor_swap_mid (a b c : Bool) : xor a (xor b c) = xor b (xor a c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem xor_comm2 (a b : Bool) : xor a b = xor b a := by
  cases a <;> cases b <;> rfl

theorem xor_perm4_last_first (a b c d : Bool) :
    xor d (xor b (xor c a)) = xor a (xor b (xor c d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem xor_rev4 (a b c d : Bool) :
    xor d (xor c (xor b a)) = xor a (xor b (xor c d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem surfaceParity0 (E : Fin 10 -> Pauli) :
    vectorParity (surfaceStabilizer (0 : StabIdx)) E =
      (anticommute Pauli.Z (E (0 : Fin 10)) ^^
        (anticommute Pauli.Z (E (1 : Fin 10)) ^^
          (anticommute Pauli.Z (E (3 : Fin 10)) ^^
            anticommute Pauli.Z (E (4 : Fin 10))))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s0,
    ← anticommute_eq_paper, anticommute, QStab.QClifford.SurfaceD3Distance.physOfData]

theorem surfaceParity1 (E : Fin 10 -> Pauli) :
    vectorParity (surfaceStabilizer (1 : StabIdx)) E =
      (anticommute Pauli.X (E (1 : Fin 10)) ^^
        (anticommute Pauli.X (E (2 : Fin 10)) ^^
          (anticommute Pauli.X (E (4 : Fin 10)) ^^
            anticommute Pauli.X (E (5 : Fin 10))))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s1,
    ← anticommute_eq_paper, anticommute, QStab.QClifford.SurfaceD3Distance.physOfData]

theorem surfaceParity2 (E : Fin 10 -> Pauli) :
    vectorParity (surfaceStabilizer (2 : StabIdx)) E =
      (anticommute Pauli.X (E (3 : Fin 10)) ^^
        (anticommute Pauli.X (E (4 : Fin 10)) ^^
          (anticommute Pauli.X (E (6 : Fin 10)) ^^
            anticommute Pauli.X (E (7 : Fin 10))))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s2,
    ← anticommute_eq_paper, anticommute, QStab.QClifford.SurfaceD3Distance.physOfData]

theorem surfaceParity3 (E : Fin 10 -> Pauli) :
    vectorParity (surfaceStabilizer (3 : StabIdx)) E =
      (anticommute Pauli.Z (E (4 : Fin 10)) ^^
        (anticommute Pauli.Z (E (5 : Fin 10)) ^^
          (anticommute Pauli.Z (E (7 : Fin 10)) ^^
            anticommute Pauli.Z (E (8 : Fin 10))))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s3,
    ← anticommute_eq_paper, anticommute, QStab.QClifford.SurfaceD3Distance.physOfData]

theorem surfaceParity4 (E : Fin 10 -> Pauli) :
    vectorParity (surfaceStabilizer (4 : StabIdx)) E =
      (anticommute Pauli.X (E (0 : Fin 10)) ^^
        anticommute Pauli.X (E (1 : Fin 10))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s4,
    ← anticommute_eq_paper, anticommute, QStab.QClifford.SurfaceD3Distance.physOfData]

theorem surfaceParity5 (E : Fin 10 -> Pauli) :
    vectorParity (surfaceStabilizer (5 : StabIdx)) E =
      (anticommute Pauli.Z (E (2 : Fin 10)) ^^
        anticommute Pauli.Z (E (5 : Fin 10))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s5,
    ← anticommute_eq_paper, anticommute, QStab.QClifford.SurfaceD3Distance.physOfData]

theorem surfaceParity6 (E : Fin 10 -> Pauli) :
    vectorParity (surfaceStabilizer (6 : StabIdx)) E =
      (anticommute Pauli.Z (E (3 : Fin 10)) ^^
        anticommute Pauli.Z (E (6 : Fin 10))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s6,
    ← anticommute_eq_paper, anticommute, QStab.QClifford.SurfaceD3Distance.physOfData]

theorem surfaceParity7 (E : Fin 10 -> Pauli) :
    vectorParity (surfaceStabilizer (7 : StabIdx)) E =
      (anticommute Pauli.X (E (7 : Fin 10)) ^^
        anticommute Pauli.X (E (8 : Fin 10))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s7,
    ← anticommute_eq_paper, anticommute, QStab.QClifford.SurfaceD3Distance.physOfData]

theorem surfaceCentralizer_to_geo (E : DataPauli)
    (h : Centralizer surfaceSpec (fullOfData E)) :
    QStab.Paper.SurfaceD3CircuitDistance.Centralizer E := by
  intro i
  have hi := h i
  simpa [surfaceSpec, surfaceStabilizer, parity, vectorParity_fullOfData] using hi

macro "surface_syn_simp" : tactic =>
  `(tactic|
    (unfold gadgetMeasFlip syndromeBit xorBools parity vectorParity surfaceSpec surfaceGadget surfaceStabilizer
      fullOfData stateOfPauliAtDetector QStab.QClifford.SurfaceD3Distance.G0
      QStab.QClifford.SurfaceD3Distance.G1 QStab.QClifford.SurfaceD3Distance.G2
      QStab.QClifford.SurfaceD3Distance.G3 QStab.QClifford.SurfaceD3Distance.G4
      QStab.QClifford.SurfaceD3Distance.G5 QStab.QClifford.SurfaceD3Distance.G6
      QStab.QClifford.SurfaceD3Distance.G7
      QStab.QClifford.SurfaceD3Distance.zGadget
      QStab.QClifford.SurfaceD3Distance.xGadget
      QStab.QClifford.SurfaceD3Distance.G0Order
      QStab.QClifford.SurfaceD3Distance.G1Order
      QStab.QClifford.SurfaceD3Distance.G2Order
      QStab.QClifford.SurfaceD3Distance.G3Order
      QStab.QClifford.SurfaceD3Distance.G4Order
      QStab.QClifford.SurfaceD3Distance.G5Order
      QStab.QClifford.SurfaceD3Distance.G6Order
      QStab.QClifford.SurfaceD3Distance.G7Order
      QStab.QClifford.SurfaceD3Distance.qq
      QStab.QClifford.SurfaceD3Distance.dq
      QStab.QClifford.SurfaceD3Distance.physOfData
     simp [List.finRange, propagateCircuit, propagateGate, eraseFaults, anticommute_eq_paper,
      QStab.Paper.SurfaceD3CircuitDistance.anticommutes,
      QStab.Paper.SurfaceD3CircuitDistance.stabAt,
      QStab.Paper.SurfaceD3CircuitDistance.s0,
      QStab.Paper.SurfaceD3CircuitDistance.s1,
      QStab.Paper.SurfaceD3CircuitDistance.s2,
      QStab.Paper.SurfaceD3CircuitDistance.s3,
      QStab.Paper.SurfaceD3CircuitDistance.s4,
      QStab.Paper.SurfaceD3CircuitDistance.s5,
      QStab.Paper.SurfaceD3CircuitDistance.s6,
      QStab.Paper.SurfaceD3CircuitDistance.s7]))

theorem surfaceSyn :
    ∀ i E,
      gadgetMeasFlip QStab.QClifford.SurfaceD3Distance.C_NZ_D3 surfaceSpec i E =
        parity surfaceSpec (surfaceSpec.stabilizer i) E := by
  intro i E
  fin_cases i
  · change syndromeBit surfaceSpec
      (propagateCircuit (eraseFaults QStab.QClifford.SurfaceD3Distance.G0)
        (stateOfPauliAtDetector 0 E))
        (⟨0, by decide⟩ : Fin surfaceSpec.numStab) =
      vectorParity (surfaceStabilizer (0 : StabIdx)) E
    rw [surfaceParity0]
    unfold syndromeBit xorBools surfaceSpec stateOfPauliAtDetector
      QStab.QClifford.SurfaceD3Distance.G0
      QStab.QClifford.SurfaceD3Distance.zGadget
      QStab.QClifford.SurfaceD3Distance.G0Order
      QStab.QClifford.SurfaceD3Distance.qq
      QStab.QClifford.SurfaceD3Distance.dq
      QStab.QClifford.SurfaceD3Distance.physOfData
    simp [propagateCircuit, propagateGate, eraseFaults]
    exact xor_perm4_last_first _ _ _ _
  · change syndromeBit surfaceSpec
      (propagateCircuit (eraseFaults QStab.QClifford.SurfaceD3Distance.G1)
        (stateOfPauliAtDetector 1 E))
        (⟨1, by decide⟩ : Fin surfaceSpec.numStab) =
      vectorParity (surfaceStabilizer (1 : StabIdx)) E
    rw [surfaceParity1]
    unfold syndromeBit xorBools surfaceSpec stateOfPauliAtDetector
      QStab.QClifford.SurfaceD3Distance.G1
      QStab.QClifford.SurfaceD3Distance.xGadget
      QStab.QClifford.SurfaceD3Distance.G1Order
      QStab.QClifford.SurfaceD3Distance.qq
      QStab.QClifford.SurfaceD3Distance.dq
      QStab.QClifford.SurfaceD3Distance.physOfData
    simp [propagateCircuit, propagateGate, eraseFaults]
    exact xor_rev4 _ _ _ _
  · change syndromeBit surfaceSpec
      (propagateCircuit (eraseFaults QStab.QClifford.SurfaceD3Distance.G2)
        (stateOfPauliAtDetector 2 E))
        (⟨2, by decide⟩ : Fin surfaceSpec.numStab) =
      vectorParity (surfaceStabilizer (2 : StabIdx)) E
    rw [surfaceParity2]
    unfold syndromeBit xorBools surfaceSpec stateOfPauliAtDetector
      QStab.QClifford.SurfaceD3Distance.G2
      QStab.QClifford.SurfaceD3Distance.xGadget
      QStab.QClifford.SurfaceD3Distance.G2Order
      QStab.QClifford.SurfaceD3Distance.qq
      QStab.QClifford.SurfaceD3Distance.dq
      QStab.QClifford.SurfaceD3Distance.physOfData
    simp [propagateCircuit, propagateGate, eraseFaults]
    exact xor_rev4 _ _ _ _
  · change syndromeBit surfaceSpec
      (propagateCircuit (eraseFaults QStab.QClifford.SurfaceD3Distance.G3)
        (stateOfPauliAtDetector 3 E))
        (⟨3, by decide⟩ : Fin surfaceSpec.numStab) =
      vectorParity (surfaceStabilizer (3 : StabIdx)) E
    rw [surfaceParity3]
    unfold syndromeBit xorBools surfaceSpec stateOfPauliAtDetector
      QStab.QClifford.SurfaceD3Distance.G3
      QStab.QClifford.SurfaceD3Distance.zGadget
      QStab.QClifford.SurfaceD3Distance.G3Order
      QStab.QClifford.SurfaceD3Distance.qq
      QStab.QClifford.SurfaceD3Distance.dq
      QStab.QClifford.SurfaceD3Distance.physOfData
    simp [propagateCircuit, propagateGate, eraseFaults]
    exact xor_perm4_last_first _ _ _ _
  · change syndromeBit surfaceSpec
      (propagateCircuit (eraseFaults QStab.QClifford.SurfaceD3Distance.G4)
        (stateOfPauliAtDetector 4 E))
        (⟨4, by decide⟩ : Fin surfaceSpec.numStab) =
      vectorParity (surfaceStabilizer (4 : StabIdx)) E
    rw [surfaceParity4]
    unfold syndromeBit xorBools surfaceSpec stateOfPauliAtDetector
      QStab.QClifford.SurfaceD3Distance.G4
      QStab.QClifford.SurfaceD3Distance.xGadget
      QStab.QClifford.SurfaceD3Distance.G4Order
      QStab.QClifford.SurfaceD3Distance.qq
      QStab.QClifford.SurfaceD3Distance.dq
      QStab.QClifford.SurfaceD3Distance.physOfData
    simp [propagateCircuit, propagateGate, eraseFaults]
    exact xor_comm2 _ _
  · change syndromeBit surfaceSpec
      (propagateCircuit (eraseFaults QStab.QClifford.SurfaceD3Distance.G5)
        (stateOfPauliAtDetector 5 E))
        (⟨5, by decide⟩ : Fin surfaceSpec.numStab) =
      vectorParity (surfaceStabilizer (5 : StabIdx)) E
    rw [surfaceParity5]
    unfold syndromeBit xorBools surfaceSpec stateOfPauliAtDetector
      QStab.QClifford.SurfaceD3Distance.G5
      QStab.QClifford.SurfaceD3Distance.zGadget
      QStab.QClifford.SurfaceD3Distance.G5Order
      QStab.QClifford.SurfaceD3Distance.qq
      QStab.QClifford.SurfaceD3Distance.dq
      QStab.QClifford.SurfaceD3Distance.physOfData
    simp [propagateCircuit, propagateGate, eraseFaults]
    exact xor_comm2 _ _
  · change syndromeBit surfaceSpec
      (propagateCircuit (eraseFaults QStab.QClifford.SurfaceD3Distance.G6)
        (stateOfPauliAtDetector 6 E))
        (⟨6, by decide⟩ : Fin surfaceSpec.numStab) =
      vectorParity (surfaceStabilizer (6 : StabIdx)) E
    rw [surfaceParity6]
    unfold syndromeBit xorBools surfaceSpec stateOfPauliAtDetector
      QStab.QClifford.SurfaceD3Distance.G6
      QStab.QClifford.SurfaceD3Distance.zGadget
      QStab.QClifford.SurfaceD3Distance.G6Order
      QStab.QClifford.SurfaceD3Distance.qq
      QStab.QClifford.SurfaceD3Distance.dq
      QStab.QClifford.SurfaceD3Distance.physOfData
    simp [propagateCircuit, propagateGate, eraseFaults]
    exact xor_comm2 _ _
  · change syndromeBit surfaceSpec
      (propagateCircuit (eraseFaults QStab.QClifford.SurfaceD3Distance.G7)
        (stateOfPauliAtDetector 7 E))
        (⟨7, by decide⟩ : Fin surfaceSpec.numStab) =
      vectorParity (surfaceStabilizer (7 : StabIdx)) E
    rw [surfaceParity7]
    unfold syndromeBit xorBools surfaceSpec stateOfPauliAtDetector
      QStab.QClifford.SurfaceD3Distance.G7
      QStab.QClifford.SurfaceD3Distance.xGadget
      QStab.QClifford.SurfaceD3Distance.G7Order
      QStab.QClifford.SurfaceD3Distance.qq
      QStab.QClifford.SurfaceD3Distance.dq
      QStab.QClifford.SurfaceD3Distance.physOfData
    simp [propagateCircuit, propagateGate, eraseFaults]
    exact xor_comm2 _ _

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 50000 in
theorem prodStab_surface :
    ∀ mask : Fin surfaceSpec.numStab -> Bool,
      prodStab surfaceSpec mask =
        fullOfData (QStab.Paper.SurfaceD3CircuitDistance.prodStab mask) := by
  decide +revert

theorem dataVector_fullOfData (E : DataPauli) :
    dataVector surfaceSpec { paulis := fullOfData E, measFlips := fun _ => false } =
      fullOfData E := by
  funext q
  by_cases h : q.val < 9
  · simp [dataVector, surfaceSpec, fullOfData, h]
  · simp [dataVector, surfaceSpec, fullOfData, h]

theorem surfaceStab_to_geo (E : DataPauli)
    (h : Stab surfaceSpec (fullOfData E)) :
    QStab.Paper.SurfaceD3CircuitDistance.Stab E := by
  rcases h with ⟨mask, hmask⟩
  unfold QStab.Paper.SurfaceD3CircuitDistance.Stab
  apply Finset.card_pos.mpr
  refine ⟨mask, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  funext d
  have hq := hmask (QStab.QClifford.SurfaceD3Distance.physOfData d)
  have hprod := congrFun (prodStab_surface mask) (QStab.QClifford.SurfaceD3Distance.physOfData d)
  rw [hprod] at hq
  simpa [fullOfData, QStab.QClifford.SurfaceD3Distance.physOfData] using hq

theorem surfaceStab_of_geo (E : DataPauli)
    (h : QStab.Paper.SurfaceD3CircuitDistance.Stab E) :
    Stab surfaceSpec (fullOfData E) := by
  unfold QStab.Paper.SurfaceD3CircuitDistance.Stab at h
  obtain ⟨mask, hmask⟩ := Finset.card_pos.mp h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmask
  refine ⟨mask, ?_⟩
  intro q
  have hprod := congrFun (prodStab_surface mask) q
  rw [hprod]
  by_cases hq : q.val < 9
  · have hd := congrFun hmask ⟨q.val, hq⟩
    simpa [fullOfData, hq] using hd
  · have hq9 : q = q9 := by
      apply Fin.ext
      simp [q9, QStab.QClifford.SurfaceD3Distance.qq]
      omega
    subst hq9
    simp [fullOfData, q9, QStab.QClifford.SurfaceD3Distance.qq]

theorem surfaceLogicalFailure_to_geo (es : ErrorState 10)
    (h : logicalFailure surfaceSpec es) :
    QStab.Paper.SurfaceD3CircuitDistance.LogicalAny
      (QStab.QClifford.SurfaceD3Distance.dataPart es) := by
  rcases h with ⟨hCent, hNotStab⟩
  constructor
  · apply surfaceCentralizer_to_geo
    simpa [dataVector_surface es] using hCent
  · intro hStab
    apply hNotStab
    have hGen := surfaceStab_of_geo (QStab.QClifford.SurfaceD3Distance.dataPart es) hStab
    simpa [dataVector_surface es] using hGen

theorem surfaceLogicalFailure_of_geo (E : DataPauli)
    (h : QStab.Paper.SurfaceD3CircuitDistance.LogicalAny E) :
    logicalFailure surfaceSpec { paulis := fullOfData E, measFlips := fun _ => false } := by
  rcases h with ⟨hCent, hNotStab⟩
  constructor
  · intro i
    have hi := hCent i
    change vectorParity (surfaceSpec.stabilizer i)
      (dataVector surfaceSpec { paulis := fullOfData E, measFlips := fun _ => false }) = false
    rw [dataVector_fullOfData E]
    simpa [surfaceSpec, surfaceStabilizer, parity, vectorParity_fullOfData] using hi
  · intro hStab
    apply hNotStab
    apply surfaceStab_to_geo E
    simpa [dataVector_fullOfData] using hStab

theorem surfaceLogicalFailure_of_geo_data (es : ErrorState 10)
    (h : QStab.Paper.SurfaceD3CircuitDistance.LogicalAny
      (QStab.QClifford.SurfaceD3Distance.dataPart es)) :
    logicalFailure surfaceSpec es := by
  rcases h with ⟨hCent, hNotStab⟩
  constructor
  · intro i
    rw [dataVector_surface es]
    simpa [surfaceSpec, surfaceStabilizer, parity, vectorParity_fullOfData] using hCent i
  · intro hStab
    apply hNotStab
    apply surfaceStab_to_geo
    simpa [dataVector_surface es] using hStab

theorem rowSpreadX_le_three (E : DataPauli) :
    QStab.Paper.SurfaceD3CircuitDistance.rowSpreadX E <= 3 := by
  unfold QStab.Paper.SurfaceD3CircuitDistance.rowSpreadX
    QStab.Paper.SurfaceD3CircuitDistance.bcount3
  by_cases h0 : QStab.Paper.SurfaceD3CircuitDistance.rowHasXb E 0 <;>
    by_cases h1 : QStab.Paper.SurfaceD3CircuitDistance.rowHasXb E 1 <;>
      by_cases h2 : QStab.Paper.SurfaceD3CircuitDistance.rowHasXb E 2 <;>
        simp [h0, h1, h2]

theorem colSpreadZ_le_three (E : DataPauli) :
    QStab.Paper.SurfaceD3CircuitDistance.colSpreadZ E <= 3 := by
  unfold QStab.Paper.SurfaceD3CircuitDistance.colSpreadZ
    QStab.Paper.SurfaceD3CircuitDistance.bcount3
  by_cases h0 : QStab.Paper.SurfaceD3CircuitDistance.colHasZb E 0 <;>
    by_cases h1 : QStab.Paper.SurfaceD3CircuitDistance.colHasZb E 1 <;>
      by_cases h2 : QStab.Paper.SurfaceD3CircuitDistance.colHasZb E 2 <;>
        simp [h0, h1, h2]

theorem BI_PAIR_three (E : DataPauli) :
    QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR E 3 := by
  constructor
  · exact QStab.Paper.SurfaceD3CircuitDistance.XRowsLe_of_mask
      (QStab.Paper.SurfaceD3CircuitDistance.maskConst 0)
      (le_trans (rowSpreadX_le_three E) (by omega))
  · exact QStab.Paper.SurfaceD3CircuitDistance.ZColsLe_of_mask
      (QStab.Paper.SurfaceD3CircuitDistance.maskConst 0)
      (le_trans (colSpreadZ_le_three E) (by omega))

theorem BI_PAIR_surfaceBarrierData (E : DataPauli) :
    QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR E (surfaceBarrierData E) := by
  unfold surfaceBarrierData
  split
  · assumption
  next h0 =>
    split
    · assumption
    next h1 =>
      split
      · assumption
      · exact BI_PAIR_three E

theorem surfaceBarrierData_le_of_BI_PAIR {E : DataPauli} {f : Nat}
    (hBI : QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR E f) :
    surfaceBarrierData E <= f := by
  unfold surfaceBarrierData
  split
  · omega
  next h0 =>
    split
    · by_cases hf0 : f = 0
      · subst f
        contradiction
      · omega
    next h1 =>
      split
      · by_cases hf0 : f = 0
        · subst f
          contradiction
        · by_cases hf1 : f = 1
          · subst f
            contradiction
          · omega
      next h2 =>
        by_cases hf0 : f = 0
        · subst f
          contradiction
        · by_cases hf1 : f = 1
          · subst f
            contradiction
          · by_cases hf2 : f = 2
            · subst f
              contradiction
            · omega

theorem surfaceBarrierData_step {E D : DataPauli}
    (hD : QStab.Paper.SurfaceD3CircuitDistance.DeltaSafe D) :
    surfaceBarrierData (QStab.Paper.SurfaceD3CircuitDistance.pmul E D) <=
      surfaceBarrierData E + 1 := by
  apply surfaceBarrierData_le_of_BI_PAIR
  exact QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR_pmul_of_delta_safe
    (BI_PAIR_surfaceBarrierData E) hD

theorem surfaceSiteSafe_of_QSiteSafe {q : Fin 10} {suffix : Circuit 10}
    (hSafe : QStab.QClifford.SurfaceD3Distance.QSiteSafe q suffix) :
    SiteSafeBeta surfaceBarrier ⟨q, suffix⟩ := by
  intro es p hp
  unfold surfaceBarrier
  rw [QStab.QClifford.SurfaceD3Distance.dataPart_propagate_inject suffix es q p]
  exact surfaceBarrierData_step
    (QStab.Paper.SurfaceD3CircuitDistance.DeltaSafe_of_fast (hSafe p hp))

theorem surfaceStep_of_allSitesSafe :
    ∀ fc : FCircuit 10,
      QStab.QClifford.SurfaceD3Distance.AllSitesSafe fc ->
      ∀ site, site ∈ errLocsWithSuffix fc -> SiteSafeBeta surfaceBarrier site
  | [], _, site, hmem => by cases hmem
  | .gate _ :: rest, hSafe, site, hmem => by
      exact surfaceStep_of_allSitesSafe rest hSafe site (by simpa [errLocsWithSuffix] using hmem)
  | .errLoc q :: rest, hSafe, site, hmem => by
      cases hmem with
      | head =>
          exact surfaceSiteSafe_of_QSiteSafe hSafe.1
      | tail _ hTail =>
          exact surfaceStep_of_allSitesSafe rest hSafe.2 site hTail

theorem surfaceStep :
    ∀ i, ∀ site, site ∈ errLocsWithSuffix (surfaceSpec.gadget i) ->
      SiteSafeBeta surfaceBarrier site := by
  intro i
  fin_cases i
  · simpa [surfaceSpec, surfaceGadget] using
      surfaceStep_of_allSitesSafe QStab.QClifford.SurfaceD3Distance.G0
        QStab.QClifford.SurfaceD3Distance.allSitesSafe_G0
  · simpa [surfaceSpec, surfaceGadget] using
      surfaceStep_of_allSitesSafe QStab.QClifford.SurfaceD3Distance.G1
        QStab.QClifford.SurfaceD3Distance.allSitesSafe_G1
  · simpa [surfaceSpec, surfaceGadget] using
      surfaceStep_of_allSitesSafe QStab.QClifford.SurfaceD3Distance.G2
        QStab.QClifford.SurfaceD3Distance.allSitesSafe_G2
  · simpa [surfaceSpec, surfaceGadget] using
      surfaceStep_of_allSitesSafe QStab.QClifford.SurfaceD3Distance.G3
        QStab.QClifford.SurfaceD3Distance.allSitesSafe_G3
  · simpa [surfaceSpec, surfaceGadget] using
      surfaceStep_of_allSitesSafe QStab.QClifford.SurfaceD3Distance.G4
        QStab.QClifford.SurfaceD3Distance.allSitesSafe_G4
  · simpa [surfaceSpec, surfaceGadget] using
      surfaceStep_of_allSitesSafe QStab.QClifford.SurfaceD3Distance.G5
        QStab.QClifford.SurfaceD3Distance.allSitesSafe_G5
  · simpa [surfaceSpec, surfaceGadget] using
      surfaceStep_of_allSitesSafe QStab.QClifford.SurfaceD3Distance.G6
        QStab.QClifford.SurfaceD3Distance.allSitesSafe_G6
  · simpa [surfaceSpec, surfaceGadget] using
      surfaceStep_of_allSitesSafe QStab.QClifford.SurfaceD3Distance.G7
        QStab.QClifford.SurfaceD3Distance.allSitesSafe_G7

theorem surfacePreserve :
    ∀ i, ∀ es, surfaceBarrier
        (propagateCircuit (eraseFaults (surfaceSpec.gadget i)) es) = surfaceBarrier es := by
  intro i es
  fin_cases i <;>
    unfold surfaceBarrier <;>
    simp [surfaceSpec, surfaceGadget,
      QStab.QClifford.SurfaceD3Distance.dataPart_det_zGadget,
      QStab.QClifford.SurfaceD3Distance.dataPart_det_xGadget,
      QStab.QClifford.SurfaceD3Distance.G0,
      QStab.QClifford.SurfaceD3Distance.G1,
      QStab.QClifford.SurfaceD3Distance.G2,
      QStab.QClifford.SurfaceD3Distance.G3,
      QStab.QClifford.SurfaceD3Distance.G4,
      QStab.QClifford.SurfaceD3Distance.G5,
      QStab.QClifford.SurfaceD3Distance.G6,
      QStab.QClifford.SurfaceD3Distance.G7]

theorem surfaceInit : surfaceBarrier (ErrorState.clean 10) = 0 := by
  unfold surfaceBarrier surfaceBarrierData
  have hData :
      QStab.QClifford.SurfaceD3Distance.dataPart (ErrorState.clean 10) =
        QStab.Paper.SurfaceD3CircuitDistance.dataI := by
    funext q
    simp [QStab.QClifford.SurfaceD3Distance.dataPart,
      QStab.Paper.SurfaceD3CircuitDistance.dataI, ErrorState.clean]
  rw [hData]
  simp [QStab.Paper.SurfaceD3CircuitDistance.OBL_INIT]

theorem surfaceDist :
    ∀ es, logicalFailure surfaceSpec es -> surfaceSpec.d <= surfaceBarrier es := by
  intro es hFail
  change 3 <= surfaceBarrier es
  unfold surfaceBarrier
  have hGeo := surfaceLogicalFailure_to_geo es hFail
  by_contra hnot
  have hlt : surfaceBarrierData (QStab.QClifford.SurfaceD3Distance.dataPart es) < 3 := by
    omega
  have hBI := BI_PAIR_surfaceBarrierData (QStab.QClifford.SurfaceD3Distance.dataPart es)
  interval_cases hf : surfaceBarrierData (QStab.QClifford.SurfaceD3Distance.dataPart es)
  · exact QStab.Paper.SurfaceD3CircuitDistance.OBL_DIST_lt3
      (QStab.QClifford.SurfaceD3Distance.dataPart es) hGeo ⟨0, by decide⟩ hBI
  · exact QStab.Paper.SurfaceD3CircuitDistance.OBL_DIST_lt3
      (QStab.QClifford.SurfaceD3Distance.dataPart es) hGeo ⟨1, by decide⟩ hBI
  · exact QStab.Paper.SurfaceD3CircuitDistance.OBL_DIST_lt3
      (QStab.QClifford.SurfaceD3Distance.dataPart es) hGeo ⟨2, by decide⟩ hBI

theorem surfaceProgramEq :
    QStab.QClifford.SurfaceD3Distance.C_NZ_D3 = specCircuit surfaceSpec := by
  simp [specCircuit, surfaceSpec, surfaceGadget, QStab.QClifford.SurfaceD3Distance.C_NZ_D3,
    List.finRange]

theorem surfaceWF :
    WellFormed QStab.QClifford.SurfaceD3Distance.C_NZ_D3 surfaceSpec := by
  rfl

theorem surfaceReachScript_faults :
    (runFScript QStab.QClifford.SurfaceD3Distance.C_NZ_D3
      QStab.QClifford.SurfaceD3Distance.reachLogicalXScript
      (ErrorState.clean 10)).2 = surfaceSpec.d := by
  unfold surfaceSpec
  unfold QStab.QClifford.SurfaceD3Distance.C_NZ_D3
    QStab.QClifford.SurfaceD3Distance.G0 QStab.QClifford.SurfaceD3Distance.G1
    QStab.QClifford.SurfaceD3Distance.G2 QStab.QClifford.SurfaceD3Distance.G3
    QStab.QClifford.SurfaceD3Distance.G4 QStab.QClifford.SurfaceD3Distance.G5
    QStab.QClifford.SurfaceD3Distance.G6 QStab.QClifford.SurfaceD3Distance.G7
    QStab.QClifford.SurfaceD3Distance.zGadget
    QStab.QClifford.SurfaceD3Distance.xGadget
    QStab.QClifford.SurfaceD3Distance.G0Order
    QStab.QClifford.SurfaceD3Distance.G1Order
    QStab.QClifford.SurfaceD3Distance.G2Order
    QStab.QClifford.SurfaceD3Distance.G3Order
    QStab.QClifford.SurfaceD3Distance.G4Order
    QStab.QClifford.SurfaceD3Distance.G5Order
    QStab.QClifford.SurfaceD3Distance.G6Order
    QStab.QClifford.SurfaceD3Distance.G7Order
    QStab.QClifford.SurfaceD3Distance.reachLogicalXScript
    runFScript
  decide

theorem surfaceReachScript_data :
    QStab.QClifford.SurfaceD3Distance.dataPart
      (runFScript QStab.QClifford.SurfaceD3Distance.C_NZ_D3
        QStab.QClifford.SurfaceD3Distance.reachLogicalXScript
        (ErrorState.clean 10)).1 =
      QStab.Paper.SurfaceD3CircuitDistance.logicalX := by
  funext q
  fin_cases q <;>
    unfold QStab.QClifford.SurfaceD3Distance.C_NZ_D3
      QStab.QClifford.SurfaceD3Distance.G0 QStab.QClifford.SurfaceD3Distance.G1
      QStab.QClifford.SurfaceD3Distance.G2 QStab.QClifford.SurfaceD3Distance.G3
      QStab.QClifford.SurfaceD3Distance.G4 QStab.QClifford.SurfaceD3Distance.G5
      QStab.QClifford.SurfaceD3Distance.G6 QStab.QClifford.SurfaceD3Distance.G7
      QStab.QClifford.SurfaceD3Distance.zGadget
      QStab.QClifford.SurfaceD3Distance.xGadget
      QStab.QClifford.SurfaceD3Distance.G0Order
      QStab.QClifford.SurfaceD3Distance.G1Order
      QStab.QClifford.SurfaceD3Distance.G2Order
      QStab.QClifford.SurfaceD3Distance.G3Order
      QStab.QClifford.SurfaceD3Distance.G4Order
      QStab.QClifford.SurfaceD3Distance.G5Order
      QStab.QClifford.SurfaceD3Distance.G6Order
      QStab.QClifford.SurfaceD3Distance.G7Order
      QStab.QClifford.SurfaceD3Distance.reachLogicalXScript
      runFScript QStab.QClifford.SurfaceD3Distance.dataPart
      QStab.QClifford.SurfaceD3Distance.physOfData
      QStab.QClifford.SurfaceD3Distance.qq
      QStab.QClifford.SurfaceD3Distance.dq <;>
    decide

theorem surfaceReachScript_undetected :
    undetected surfaceSpec
      (runFScript QStab.QClifford.SurfaceD3Distance.C_NZ_D3
        QStab.QClifford.SurfaceD3Distance.reachLogicalXScript
        (ErrorState.clean 10)).1 := by
  intro i
  fin_cases i <;>
    unfold syndromeBit xorBools surfaceSpec QStab.QClifford.SurfaceD3Distance.C_NZ_D3
      QStab.QClifford.SurfaceD3Distance.G0 QStab.QClifford.SurfaceD3Distance.G1
      QStab.QClifford.SurfaceD3Distance.G2 QStab.QClifford.SurfaceD3Distance.G3
      QStab.QClifford.SurfaceD3Distance.G4 QStab.QClifford.SurfaceD3Distance.G5
      QStab.QClifford.SurfaceD3Distance.G6 QStab.QClifford.SurfaceD3Distance.G7
      QStab.QClifford.SurfaceD3Distance.zGadget
      QStab.QClifford.SurfaceD3Distance.xGadget
      QStab.QClifford.SurfaceD3Distance.G0Order
      QStab.QClifford.SurfaceD3Distance.G1Order
      QStab.QClifford.SurfaceD3Distance.G2Order
      QStab.QClifford.SurfaceD3Distance.G3Order
      QStab.QClifford.SurfaceD3Distance.G4Order
      QStab.QClifford.SurfaceD3Distance.G5Order
      QStab.QClifford.SurfaceD3Distance.G6Order
      QStab.QClifford.SurfaceD3Distance.G7Order
      QStab.QClifford.SurfaceD3Distance.reachLogicalXScript
      runFScript QStab.QClifford.SurfaceD3Distance.qq
      QStab.QClifford.SurfaceD3Distance.dq
      QStab.QClifford.SurfaceD3Distance.physOfData <;>
    decide

def twoDetectorFireState : ErrorState 10 :=
  { ErrorState.clean 10 with
    detectors := fun k => decide (k = 0) || decide (k = 1) }

theorem surfaceTwoDetector_not_undetected :
    ¬ undetected surfaceSpec twoDetectorFireState := by
  intro h
  have h0 := h ⟨0, by decide⟩
  simp [syndromeBit, xorBools, twoDetectorFireState, surfaceSpec] at h0

theorem surfaceReachOk :
    (runFScript QStab.QClifford.SurfaceD3Distance.C_NZ_D3
      QStab.QClifford.SurfaceD3Distance.reachLogicalXScript
      (ErrorState.clean 10)).2 = surfaceSpec.d ∧
      failure surfaceSpec
        (runFScript QStab.QClifford.SurfaceD3Distance.C_NZ_D3
          QStab.QClifford.SurfaceD3Distance.reachLogicalXScript
          (ErrorState.clean 10)).1 := by
  constructor
  · exact surfaceReachScript_faults
  · constructor
    · apply surfaceLogicalFailure_of_geo_data
      have hData := surfaceReachScript_data
      simpa [hData] using QStab.Paper.SurfaceD3CircuitDistance.logicalX_real
    · constructor
      · exact surfaceReachScript_undetected
      · intro i hi
        simp [surfaceSpec] at hi

theorem surfaceSyntax_isData_eq (q : Fin 10) :
    surfaceSyntaxSpec.isData q = surfaceSpec.isData q := by
  fin_cases q <;> rfl

set_option maxHeartbeats 1000000 in
theorem surfaceSyntax_stabilizer_eq (i : Fin surfaceSyntaxSpec.numStab) :
    surfaceSyntaxSpec.stabilizer i = surfaceSpec.stabilizer i := by
  fin_cases i <;> funext q <;> fin_cases q <;> rfl

theorem surfaceSyntax_readout_eq (i : Fin surfaceSyntaxSpec.numStab) :
    surfaceSyntaxSpec.stabilizerReadout i = surfaceSpec.stabilizerReadout i := by
  fin_cases i <;> rfl

theorem surfaceSyntax_gadget_eq (i : Fin surfaceSyntaxSpec.numStab) :
    surfaceSyntaxSpec.gadget i = surfaceSpec.gadget i := by
  fin_cases i <;> rfl

theorem surfaceSyntax_detectorStart_eq (i : Fin surfaceSyntaxSpec.numStab) :
    surfaceSyntaxSpec.gadgetDetectorStart i = surfaceSpec.gadgetDetectorStart i := by
  fin_cases i <;> rfl

theorem surfaceSyntax_dataVector_eq (es : ErrorState 10) :
    dataVector surfaceSyntaxSpec es = dataVector surfaceSpec es := by
  funext q
  simp [dataVector, surfaceSyntax_isData_eq]

theorem surfaceSyntax_prodStab_eq (mask : Fin surfaceSyntaxSpec.numStab -> Bool) :
    prodStab surfaceSyntaxSpec mask = prodStab surfaceSpec mask := by
  funext q
  unfold prodStab
  simp [List.finRange, surfaceSyntax_stabilizer_eq]
  rfl

theorem surfaceSyntax_centralizer_iff (E : Fin 10 -> Pauli) :
    Centralizer surfaceSyntaxSpec E ↔ Centralizer surfaceSpec E := by
  constructor
  · intro h i
    have hi := h i
    simpa [surfaceSyntax_stabilizer_eq] using hi
  · intro h i
    have hi := h i
    simpa [surfaceSyntax_stabilizer_eq] using hi

theorem surfaceSyntax_stab_iff (E : Fin 10 -> Pauli) :
    Stab surfaceSyntaxSpec E ↔ Stab surfaceSpec E := by
  constructor
  · rintro ⟨mask, hmask⟩
    exact ⟨mask, by
      intro q
      rw [← surfaceSyntax_prodStab_eq mask]
      exact hmask q⟩
  · rintro ⟨mask, hmask⟩
    exact ⟨mask, by
      intro q
      rw [surfaceSyntax_prodStab_eq mask]
      exact hmask q⟩

theorem surfaceSyntax_logicalFailure_iff (es : ErrorState 10) :
    logicalFailure surfaceSyntaxSpec es ↔ logicalFailure surfaceSpec es := by
  simp [logicalFailure, surfaceSyntax_dataVector_eq, surfaceSyntax_centralizer_iff,
    surfaceSyntax_stab_iff]

theorem surfaceSyntax_undetected_iff (es : ErrorState 10) :
    undetected surfaceSyntaxSpec es ↔ undetected surfaceSpec es := by
  constructor
  · intro h i
    have hi := h i
    simpa [undetected, syndromeBit, surfaceSyntax_readout_eq] using hi
  · intro h i
    have hi := h i
    simpa [undetected, syndromeBit, surfaceSyntax_readout_eq] using hi

theorem surfaceSyntax_allPostselectionFlagsZero_iff (es : ErrorState 10) :
    allPostselectionFlagsZero surfaceSyntaxSpec es ↔
      allPostselectionFlagsZero surfaceSpec es := by
  constructor
  · intro h i hi
    have hfalse : surfaceSpec.postselectFlag i = false := rfl
    rw [hfalse] at hi
    cases hi
  · intro h i hi
    have hfalse : surfaceSyntaxSpec.postselectFlag i = false := by
      unfold surfaceSyntaxSpec VCInput.toCodeSpec VCInputSyntax.toVCInput
        ExtractionSpec.toCodeSpec ExtractionSyntax.toSpec surfaceD3SyntaxInput
        surfaceExtractionSyntax
      rw [decide_eq_false_iff_not]
      intro hmem
      cases hmem
    rw [hfalse] at hi
    cases hi

theorem surfaceSyntax_failure_iff (es : ErrorState 10) :
    failure surfaceSyntaxSpec es ↔ failure surfaceSpec es := by
  simp [failure, allFlagsZero, surfaceSyntax_logicalFailure_iff,
    surfaceSyntax_undetected_iff, surfaceSyntax_allPostselectionFlagsZero_iff]

theorem surfaceSyntax_specCircuit_eq :
    specCircuit surfaceSyntaxSpec = specCircuit surfaceSpec := by
  simp [specCircuit, List.finRange, surfaceSyntax_gadget_eq]
  rfl

theorem surfaceSyntax_syn :
    ∀ i E,
      gadgetMeasFlip QStab.QClifford.SurfaceD3Distance.C_NZ_D3 surfaceSyntaxSpec i E =
        parity surfaceSyntaxSpec (surfaceSyntaxSpec.stabilizer i) E := by
  intro i E
  have h := surfaceSyn i E
  simpa [gadgetMeasFlip, parity, syndromeBit, surfaceSyntax_readout_eq,
    surfaceSyntax_detectorStart_eq, surfaceSyntax_gadget_eq, surfaceSyntax_stabilizer_eq]
    using h

theorem surfaceSyntax_step :
    ∀ i, ∀ site, site ∈ errLocsWithSuffix (surfaceSyntaxSpec.gadget i) ->
      SiteSafeBeta surfaceBarrier site := by
  intro i site hmem
  exact surfaceStep i site (by simpa [surfaceSyntax_gadget_eq] using hmem)

theorem surfaceSyntax_preserve :
    ∀ i, ∀ es, surfaceBarrier
        (propagateCircuit (eraseFaults (surfaceSyntaxSpec.gadget i)) es) = surfaceBarrier es := by
  intro i es
  simpa [surfaceSyntax_gadget_eq] using surfacePreserve i es

theorem surfaceSyntax_dist :
    ∀ es, logicalFailure surfaceSyntaxSpec es -> surfaceSyntaxSpec.d <= surfaceBarrier es := by
  intro es hFail
  exact surfaceDist es ((surfaceSyntax_logicalFailure_iff es).mp hFail)

theorem surfaceSyntax_reachOk :
    (runFScript QStab.QClifford.SurfaceD3Distance.C_NZ_D3
      QStab.QClifford.SurfaceD3Distance.reachLogicalXScript
      (ErrorState.clean 10)).2 = surfaceSyntaxSpec.d ∧
      failure surfaceSyntaxSpec
        (runFScript QStab.QClifford.SurfaceD3Distance.C_NZ_D3
          QStab.QClifford.SurfaceD3Distance.reachLogicalXScript
          (ErrorState.clean 10)).1 := by
  constructor
  · exact surfaceReachScript_faults
  · exact (surfaceSyntax_failure_iff _).mpr surfaceReachOk.2

def surfaceD3Cert :
    DistanceCertificate QStab.QClifford.SurfaceD3Distance.C_NZ_D3 surfaceSpec where
  barrier := surfaceBarrier
  programEq := surfaceProgramEq
  wf := surfaceWF
  syn := surfaceSyn
  init := surfaceInit
  step := surfaceStep
  preserve := surfacePreserve
  dist := surfaceDist
  reachScript := QStab.QClifford.SurfaceD3Distance.reachLogicalXScript
  reachOk := surfaceReachOk

def surfaceD3SyntaxDischarge : DischargedVCs surfaceD3SyntaxInput.toVCInput where
  reachScript := QStab.QClifford.SurfaceD3Distance.reachLogicalXScript
  programEq := by
    change QStab.QClifford.SurfaceD3Distance.C_NZ_D3 = specCircuit surfaceSyntaxSpec
    rw [surfaceProgramEq]
    exact surfaceSyntax_specCircuit_eq.symm
  wf := by
    rfl
  syn := by
    simpa [vcgen, GeneratedVCs.denoteSlot, VCSlot.denote] using surfaceSyntax_syn
  ftDistance := by
    simp only [vcgen, GeneratedVCs.denoteSlot, VCSlot.denote]
    intro σ hRun hFlags
    rw [denoteQC_circuitDistanceAny]
    intro hLogical
    have hTol := certificate_tolerates surfaceD3Cert
    by_contra hlt
    push_neg at hlt
    apply hTol σ hRun (by have : surfaceD3SyntaxInput.toVCInput.toCodeSpec.d = surfaceSpec.d := rfl; omega)
    constructor
    · exact (surfaceSyntax_logicalFailure_iff σ.es).mp hLogical
    · exact ⟨(surfaceSyntax_undetected_iff σ.es).mp hFlags.1,
        (surfaceSyntax_allPostselectionFlagsZero_iff σ.es).mp hFlags.2⟩
  reachOk := by
    simpa [vcgen, GeneratedVCs.denoteSlot, VCSlot.denote] using surfaceSyntax_reachOk

def surfaceD3SyntaxVCGen : VCGen surfaceD3SyntaxInput.toVCInput :=
  .mk surfaceD3SyntaxDischarge

theorem surfaceD3_safe_from_syntax :
    Safe QStab.QClifford.SurfaceD3Distance.C_NZ_D3
      surfaceD3SyntaxInput.toVCInput.toCodeSpec :=
  vcgen_sound surfaceD3SyntaxVCGen

def surfaceD3Input : VCInput 10 :=
  VCInput.ofPCC QStab.QClifford.SurfaceD3Distance.C_NZ_D3 surfaceSpec
    .unconditional (by decide) (by decide)

def surfaceD3VCGen : VCGen surfaceD3Input :=
  VCGen.ofDistanceCertificate surfaceD3Cert (by decide) (by decide)

theorem surfaceD3_safe_vcgen :
    Safe QStab.QClifford.SurfaceD3Distance.C_NZ_D3 surfaceSpec := by
  simpa [surfaceD3Input] using vcgen_sound surfaceD3VCGen

theorem surfaceD3_safe :
    Safe QStab.QClifford.SurfaceD3Distance.C_NZ_D3 surfaceSpec :=
  surfaceD3_safe_vcgen

#print axioms surfaceD3_safe

end QStab.QClifford.PCC.SurfaceD3
