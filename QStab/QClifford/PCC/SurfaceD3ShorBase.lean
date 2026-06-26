import QStab.QClifford.PCC.SurfaceD3
import QStab.QClifford.InputFaultFT

/-!
# Surface-d3 Shor PCC: base circuit definitions

Shared by `SurfaceD3ShorGlobal` and `SurfaceD3Shor`.  Contains the concrete
circuit, code spec, policy-vector types, and elementary helpers needed by both.
-/

namespace QStab.QClifford.PCC.SurfaceD3Shor

abbrev DataQ := QStab.Paper.SurfaceD3CircuitDistance.DataQ
abbrev DataPauli := QStab.Paper.SurfaceD3CircuitDistance.DataPauli
abbrev StabIdx := QStab.Paper.SurfaceD3CircuitDistance.StabIdx

abbrev Nq : Nat := 41
abbrev NumFlags : Nat := 32

def dataPhys (q : DataQ) : Fin Nq :=
  ⟨q.val, by show q.val < 41; have := q.isLt; omega⟩

def aux (n : Nat) (h : n < Nq := by decide) : Fin Nq := ⟨n, h⟩
def flag (n : Nat) (h : n < NumFlags := by decide) : Fin NumFlags := ⟨n, h⟩

def physSchedule (order : List DataQ) : QStab.QClifford.Compile.Schedule Nq :=
  ⟨order.map dataPhys⟩

def shorConfig (cat : List (Fin Nq)) (verifier : Fin Nq) :
    QStab.QClifford.Compile.AncillaConfig Nq :=
  .shor cat verifier

def shorZGadget (order : List DataQ) (cat : List (Fin Nq)) (verifier : Fin Nq) :
    FCircuit Nq :=
  QStab.QClifford.Compile.compileGadget .Shor .Z
    (physSchedule order) (shorConfig cat verifier)

def shorXGadget (order : List DataQ) (cat : List (Fin Nq)) (verifier : Fin Nq) :
    FCircuit Nq :=
  QStab.QClifford.Compile.compileGadget .Shor .X
    (physSchedule order) (shorConfig cat verifier)

def G0Cat : List (Fin Nq) := [aux 9, aux 10, aux 11, aux 12]
def G1Cat : List (Fin Nq) := [aux 14, aux 15, aux 16, aux 17]
def G2Cat : List (Fin Nq) := [aux 19, aux 20, aux 21, aux 22]
def G3Cat : List (Fin Nq) := [aux 24, aux 25, aux 26, aux 27]
def G4Cat : List (Fin Nq) := [aux 29, aux 30]
def G5Cat : List (Fin Nq) := [aux 32, aux 33]
def G6Cat : List (Fin Nq) := [aux 35, aux 36]
def G7Cat : List (Fin Nq) := [aux 38, aux 39]

def G0 : FCircuit Nq :=
  shorZGadget QStab.QClifford.SurfaceD3Distance.G0Order G0Cat (aux 13)
def G1 : FCircuit Nq :=
  shorXGadget QStab.QClifford.SurfaceD3Distance.G1Order G1Cat (aux 18)
def G2 : FCircuit Nq :=
  shorXGadget QStab.QClifford.SurfaceD3Distance.G2Order G2Cat (aux 23)
def G3 : FCircuit Nq :=
  shorZGadget QStab.QClifford.SurfaceD3Distance.G3Order G3Cat (aux 28)
def G4 : FCircuit Nq :=
  shorXGadget QStab.QClifford.SurfaceD3Distance.G4Order G4Cat (aux 31)
def G5 : FCircuit Nq :=
  shorZGadget QStab.QClifford.SurfaceD3Distance.G5Order G5Cat (aux 34)
def G6 : FCircuit Nq :=
  shorZGadget QStab.QClifford.SurfaceD3Distance.G6Order G6Cat (aux 37)
def G7 : FCircuit Nq :=
  shorXGadget QStab.QClifford.SurfaceD3Distance.G7Order G7Cat (aux 40)

def shorSurfaceCircuit : FCircuit Nq :=
  G0 ++ (G1 ++ (G2 ++ (G3 ++ (G4 ++ (G5 ++ (G6 ++ G7))))))

def fullOfData (E : DataPauli) : Fin Nq -> Pauli :=
  fun q => if h : q.val < 9 then E ⟨q.val, h⟩ else Pauli.I

def dataPart (es : ErrorState Nq) : DataPauli :=
  fun q => es.paulis (dataPhys q)

def surfaceStabilizer (i : StabIdx) : Fin Nq -> Pauli :=
  fullOfData (QStab.Paper.SurfaceD3CircuitDistance.stabAt i)

def readout : StabIdx -> List (Fin NumFlags)
  | ⟨0, _⟩ => [flag 1, flag 2, flag 3, flag 4]
  | ⟨1, _⟩ => [flag 6, flag 7, flag 8, flag 9]
  | ⟨2, _⟩ => [flag 11, flag 12, flag 13, flag 14]
  | ⟨3, _⟩ => [flag 16, flag 17, flag 18, flag 19]
  | ⟨4, _⟩ => [flag 21, flag 22]
  | ⟨5, _⟩ => [flag 24, flag 25]
  | ⟨6, _⟩ => [flag 27, flag 28]
  | _ => [flag 30, flag 31]

def isVerifierSlot : Fin NumFlags -> Bool
  | ⟨0, _⟩ => true
  | ⟨5, _⟩ => true
  | ⟨10, _⟩ => true
  | ⟨15, _⟩ => true
  | ⟨20, _⟩ => true
  | ⟨23, _⟩ => true
  | ⟨26, _⟩ => true
  | ⟨29, _⟩ => true
  | _ => false

def gadgetStart : StabIdx -> Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 5
  | ⟨2, _⟩ => 10
  | ⟨3, _⟩ => 15
  | ⟨4, _⟩ => 20
  | ⟨5, _⟩ => 23
  | ⟨6, _⟩ => 26
  | _ => 29

def surfaceGadget : StabIdx -> FCircuit Nq
  | ⟨0, _⟩ => G0
  | ⟨1, _⟩ => G1
  | ⟨2, _⟩ => G2
  | ⟨3, _⟩ => G3
  | ⟨4, _⟩ => G4
  | ⟨5, _⟩ => G5
  | ⟨6, _⟩ => G6
  | _ => G7

def surfaceSpecShor : CodeSpec Nq where
  numStab := 8
  numFlags := NumFlags
  isData := fun q => decide (q.val < 9)
  stabilizer := surfaceStabilizer
  stabilizerReadout := readout
  postselectFlag := isVerifierSlot
  flagSlot := fun i => i.val
  flagSlot_injective := by intro a b h; exact Fin.ext h
  flagSlot_ordered := by intro i; rfl
  readout_disjoint := by decide
  gadgetDetectorStart := gadgetStart
  gadget := surfaceGadget
  expectedProgram := circuitView shorSurfaceCircuit
  d := 3
  d_pos := by decide

def surfaceBarrier (es : ErrorState Nq) : Nat :=
  SurfaceD3.surfaceBarrierData (dataPart es)

def dataProd : List DataPauli -> DataPauli
  | [] => QStab.Paper.SurfaceD3CircuitDistance.dataI
  | E :: rest => QStab.Paper.SurfaceD3CircuitDistance.pmul E (dataProd rest)

abbrev PolicyIdx : Type := Fin (surfaceSpecShor.numStab + surfaceSpecShor.numFlags)
abbrev PolicyVec : Type := PolicyIdx -> Bool

def policyObservation (es : ErrorState Nq) : PolicyVec :=
  fun k =>
    if h : k.val < surfaceSpecShor.numStab then
      syndromeBit surfaceSpecShor es ⟨k.val, h⟩
    else
      let j : Fin surfaceSpecShor.numFlags :=
        ⟨k.val - surfaceSpecShor.numStab, by have hk := k.isLt; omega⟩
      if surfaceSpecShor.postselectFlag j then
        es.detectors (surfaceSpecShor.flagSlot j)
      else
        false

def policyXor (a b : PolicyVec) : PolicyVec :=
  fun k => xor (a k) (b k)

def policyZero : PolicyVec := fun _ => false

def policyXorList : List PolicyVec -> PolicyVec
  | [] => policyZero
  | v :: rest => policyXor v (policyXorList rest)

def policyDiff (a b : ErrorState Nq) : PolicyVec :=
  policyXor (policyObservation a) (policyObservation b)

/-! ### Shared helpers -/

theorem pauli_mem_XYZ {p : Pauli} (hp : p ≠ Pauli.I) :
    p ∈ [Pauli.X, Pauli.Y, Pauli.Z] := by
  cases p <;> simp_all

theorem surfaceBarrierData_le1_implies_deltaSafe
    (E : QStab.Paper.SurfaceD3CircuitDistance.DataPauli)
    (h : QStab.QClifford.PCC.SurfaceD3.surfaceBarrierData E ≤ 1) :
    QStab.Paper.SurfaceD3CircuitDistance.DeltaSafe E := by
  by_cases h0 : QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR E 0
  · rcases h0 with ⟨hX, hZ⟩
    rcases Finset.card_pos.mp hX with ⟨mX, hmX⟩
    rcases Finset.card_pos.mp hZ with ⟨mZ, hmZ⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmX hmZ
    exact ⟨Finset.card_pos.mpr ⟨mX, by simp [Finset.mem_filter]; omega⟩,
           Finset.card_pos.mpr ⟨mZ, by simp [Finset.mem_filter]; omega⟩⟩
  · by_cases h1 : QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR E 1
    · exact h1
    · simp only [QStab.QClifford.PCC.SurfaceD3.surfaceBarrierData, h0, h1, ite_false] at h
      split_ifs at h with h2 <;> omega

private def pmulPaulisLocal {nq : Nat} (a b : Fin nq -> Pauli) : Fin nq -> Pauli :=
  fun i => pauliMul (a i) (b i)

private theorem propagateGate_paulis_mul_local {nq : Nat} (g : Gate nq)
    (a b es : ErrorState nq) (hes : es.paulis = pmulPaulisLocal a.paulis b.paulis) :
    (propagateGate g es).paulis =
      pmulPaulisLocal (propagateGate g a).paulis (propagateGate g b).paulis := by
  funext i
  have key : ∀ (x y z w : Pauli),
      pauliMul (pauliMul x y) (pauliMul z w) = pauliMul (pauliMul x z) (pauliMul y w) := by
    intro x y z w; cases x <;> cases y <;> cases z <;> cases w <;> rfl
  cases g with
  | cnot c t hne =>
      simp only [propagateGate]; rw [hes]; simp only [pmulPaulisLocal]
      split_ifs with h1 h2
      · have hx : xPart (pauliMul (a.paulis c) (b.paulis c))
            = pauliMul (xPart (a.paulis c)) (xPart (b.paulis c)) := by
          cases a.paulis c <;> cases b.paulis c <;> rfl
        rw [hx]; exact key _ _ _ _
      · have hz : zPart (pauliMul (a.paulis t) (b.paulis t))
            = pauliMul (zPart (a.paulis t)) (zPart (b.paulis t)) := by
          cases a.paulis t <;> cases b.paulis t <;> rfl
        rw [hz]; exact key _ _ _ _
      · rfl
  | hadamard q =>
      simp only [propagateGate]; rw [hes]; simp only [pmulPaulisLocal]
      split_ifs with h1
      · cases a.paulis i <;> cases b.paulis i <;> rfl
      · rfl
  | prepZero q =>
      simp only [propagateGate]; rw [hes]; simp only [pmulPaulisLocal]; split_ifs <;> rfl
  | prepPlus q =>
      simp only [propagateGate]; rw [hes]; simp only [pmulPaulisLocal]; split_ifs <;> rfl
  | measZ q => simp only [propagateGate]; rw [hes]

private theorem propagateCircuit_paulis_mul_local {nq : Nat} (c : Circuit nq)
    (a b es : ErrorState nq) (hes : es.paulis = pmulPaulisLocal a.paulis b.paulis) :
    (propagateCircuit c es).paulis =
      pmulPaulisLocal (propagateCircuit c a).paulis (propagateCircuit c b).paulis := by
  induction c generalizing a b es with
  | nil => simpa [propagateCircuit] using hes
  | cons g gs ih =>
      simp only [propagateCircuit]
      exact ih _ _ _ (propagateGate_paulis_mul_local g a b es hes)

private theorem inject_paulis_mul_local {nq : Nat} (es : ErrorState nq) (q : Fin nq) (p : Pauli) :
    (es.inject q p).paulis =
      pmulPaulisLocal es.paulis ((ErrorState.clean nq).inject q p).paulis := by
  funext i
  simp only [ErrorState.inject, ErrorState.clean, pmulPaulisLocal]
  split_ifs with h
  · cases p <;> cases es.paulis i <;> rfl
  · rw [pauliMul_I_right]

theorem dataPart_inject_factor (c : Circuit Nq) (es : ErrorState Nq)
    (q : Fin Nq) (p : Pauli) :
    dataPart (propagateCircuit c (es.inject q p)) =
      QStab.Paper.SurfaceD3CircuitDistance.pmul
        (dataPart (propagateCircuit c es))
        (dataPart (propagateCircuit c ((ErrorState.clean Nq).inject q p))) := by
  funext r
  have hfac := propagateCircuit_paulis_mul_local c es ((ErrorState.clean Nq).inject q p)
    (es.inject q p) (inject_paulis_mul_local es q p)
  simp only [dataPart, QStab.Paper.SurfaceD3CircuitDistance.pmul]
  have := congrFun hfac (dataPhys r)
  simpa [pmulPaulisLocal] using this

theorem propagateGate_paulis_congr {nq : Nat} (g : Gate nq)
    (a b : ErrorState nq) (h : a.paulis = b.paulis) :
    (propagateGate g a).paulis = (propagateGate g b).paulis := by
  cases g <;> simp only [propagateGate] <;> rw [h]

theorem propagateCircuit_paulis_congr {nq : Nat} :
    ∀ (C : Circuit nq) (a b : ErrorState nq),
      a.paulis = b.paulis → (propagateCircuit C a).paulis = (propagateCircuit C b).paulis
  | [], _, _, h => h
  | g :: gs, a, b, h => by
      simp only [propagateCircuit]
      exact propagateCircuit_paulis_congr gs _ _
        (propagateGate_paulis_congr g a b h)

end QStab.QClifford.PCC.SurfaceD3Shor