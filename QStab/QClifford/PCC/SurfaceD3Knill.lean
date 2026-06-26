import QStab.QClifford.PCC.SurfaceD3

/-!
# Surface-d3 Knill client for the QClifford PCC kernel

This file instantiates the PCC detector combiner with Knill-style raw
transversal readouts: each stabilizer syndrome is the XOR of the raw
measurements belonging to that stabilizer.
-/

namespace QStab.QClifford.PCC.SurfaceD3Knill

abbrev DataQ := QStab.Paper.SurfaceD3CircuitDistance.DataQ
abbrev DataPauli := QStab.Paper.SurfaceD3CircuitDistance.DataPauli
abbrev StabIdx := QStab.Paper.SurfaceD3CircuitDistance.StabIdx

abbrev Nq : Nat := 33
abbrev NumRaw : Nat := 24

def dq (n : Nat) (h : n < 9 := by decide) : DataQ := ⟨n, h⟩

def dataPhys (q : DataQ) : Fin Nq :=
  ⟨q.val, by
    show q.val < 33
    have := q.isLt
    omega⟩

def rawAnc (r : Fin NumRaw) : Fin Nq :=
  ⟨9 + r.val, by
    show 9 + r.val < 33
    have hr : r.val < 24 := by
      change r.val < 24
      exact r.isLt
    omega⟩

def raw (n : Nat) (h : n < NumRaw := by decide) : Fin NumRaw := ⟨n, h⟩

theorem dataPhys_ne_rawAnc (q : DataQ) (r : Fin NumRaw) :
    dataPhys q ≠ rawAnc r := by
  intro h
  have hv := congrArg Fin.val h
  simp [dataPhys, rawAnc] at hv
  have hr : r.val < 24 := by
    change r.val < 24
    exact r.isLt
  omega

def physSchedule (order : List DataQ) : QStab.QClifford.Compile.Schedule Nq :=
  ⟨order.map dataPhys⟩

def rawAncillas (slots : List (Fin NumRaw)) : List (Fin Nq) :=
  slots.map rawAnc

def knillConfig (slots : List (Fin NumRaw)) : QStab.QClifford.Compile.AncillaConfig Nq :=
  .knill (rawAncillas slots)

def G0Slots : List (Fin NumRaw) := [raw 0, raw 1, raw 2, raw 3]
def G1Slots : List (Fin NumRaw) := [raw 4, raw 5, raw 6, raw 7]
def G2Slots : List (Fin NumRaw) := [raw 8, raw 9, raw 10, raw 11]
def G3Slots : List (Fin NumRaw) := [raw 12, raw 13, raw 14, raw 15]
def G4Slots : List (Fin NumRaw) := [raw 16, raw 17]
def G5Slots : List (Fin NumRaw) := [raw 18, raw 19]
def G6Slots : List (Fin NumRaw) := [raw 20, raw 21]
def G7Slots : List (Fin NumRaw) := [raw 22, raw 23]

def knillZGadget (order : List DataQ) (slots : List (Fin NumRaw)) : FCircuit Nq :=
  QStab.QClifford.Compile.compileGadget .Knill .Z
    (physSchedule order) (knillConfig slots)

def knillXGadget (order : List DataQ) (slots : List (Fin NumRaw)) : FCircuit Nq :=
  QStab.QClifford.Compile.compileGadget .Knill .X
    (physSchedule order) (knillConfig slots)

def G0 : FCircuit Nq :=
  knillZGadget QStab.QClifford.SurfaceD3Distance.G0Order G0Slots
def G1 : FCircuit Nq :=
  knillXGadget QStab.QClifford.SurfaceD3Distance.G1Order G1Slots
def G2 : FCircuit Nq :=
  knillXGadget QStab.QClifford.SurfaceD3Distance.G2Order G2Slots
def G3 : FCircuit Nq :=
  knillZGadget QStab.QClifford.SurfaceD3Distance.G3Order G3Slots
def G4 : FCircuit Nq :=
  knillXGadget QStab.QClifford.SurfaceD3Distance.G4Order G4Slots
def G5 : FCircuit Nq :=
  knillZGadget QStab.QClifford.SurfaceD3Distance.G5Order G5Slots
def G6 : FCircuit Nq :=
  knillZGadget QStab.QClifford.SurfaceD3Distance.G6Order G6Slots
def G7 : FCircuit Nq :=
  knillXGadget QStab.QClifford.SurfaceD3Distance.G7Order G7Slots

def knillSurfaceCircuit : FCircuit Nq :=
  G0 ++ (G1 ++ (G2 ++ (G3 ++ (G4 ++ (G5 ++ (G6 ++ G7))))))

def fullOfData (E : DataPauli) : Fin Nq -> Pauli :=
  fun q => if h : q.val < 9 then E ⟨q.val, h⟩ else Pauli.I

def dataPart (es : ErrorState Nq) : DataPauli :=
  fun q => es.paulis (dataPhys q)

def surfaceStabilizer (i : StabIdx) : Fin Nq -> Pauli :=
  fullOfData (QStab.Paper.SurfaceD3CircuitDistance.stabAt i)

def readout : StabIdx -> List (Fin NumRaw)
  | ⟨0, _⟩ => G0Slots
  | ⟨1, _⟩ => G1Slots
  | ⟨2, _⟩ => G2Slots
  | ⟨3, _⟩ => G3Slots
  | ⟨4, _⟩ => G4Slots
  | ⟨5, _⟩ => G5Slots
  | ⟨6, _⟩ => G6Slots
  | _ => G7Slots

def gadgetStart : StabIdx -> Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 8
  | ⟨3, _⟩ => 12
  | ⟨4, _⟩ => 16
  | ⟨5, _⟩ => 18
  | ⟨6, _⟩ => 20
  | _ => 22

def surfaceGadget : StabIdx -> FCircuit Nq
  | ⟨0, _⟩ => G0
  | ⟨1, _⟩ => G1
  | ⟨2, _⟩ => G2
  | ⟨3, _⟩ => G3
  | ⟨4, _⟩ => G4
  | ⟨5, _⟩ => G5
  | ⟨6, _⟩ => G6
  | _ => G7

def surfaceSpecKnill : CodeSpec Nq where
  numStab := 8
  numFlags := NumRaw
  isData := fun q => decide (q.val < 9)
  stabilizer := surfaceStabilizer
  stabilizerReadout := readout
  postselectFlag := fun _ => false
  flagSlot := fun i => i.val
  flagSlot_injective := by
    intro a b h
    exact Fin.ext h
  flagSlot_ordered := by
    intro i
    rfl
  readout_disjoint := by
    decide
  gadgetDetectorStart := gadgetStart
  gadget := surfaceGadget
  expectedProgram := circuitView knillSurfaceCircuit
  d := 3
  d_pos := by decide

def surfaceBarrier (es : ErrorState Nq) : Nat :=
  SurfaceD3.surfaceBarrierData (dataPart es)

theorem dataVector_surface (es : ErrorState Nq) :
    dataVector surfaceSpecKnill es = fullOfData (dataPart es) := by
  funext q
  by_cases h : q.val < 9
  · simp [dataVector, surfaceSpecKnill, fullOfData, dataPart, dataPhys, h]
  · simp [dataVector, surfaceSpecKnill, fullOfData, h]

theorem vectorParity_fullOfData (S E : DataPauli) :
    vectorParity (fullOfData S) (fullOfData E) =
      QStab.Paper.SurfaceD3CircuitDistance.parity S E := by
  unfold vectorParity QStab.Paper.SurfaceD3CircuitDistance.parity fullOfData
  simp [Nq, List.finRange, SurfaceD3.anticommute_eq_paper,
    QStab.Paper.SurfaceD3CircuitDistance.anticommutes]

@[simp] theorem apply_finNq_0 (E : Fin Nq -> Pauli) (h : 0 < Nq) :
    E (Fin.mk 0 h) = E (0 : Fin Nq) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_finNq_1 (E : Fin Nq -> Pauli) (h : 1 < Nq) :
    E (Fin.mk 1 h) = E (1 : Fin Nq) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_finNq_2 (E : Fin Nq -> Pauli) (h : 2 < Nq) :
    E (Fin.mk 2 h) = E (2 : Fin Nq) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_finNq_3 (E : Fin Nq -> Pauli) (h : 3 < Nq) :
    E (Fin.mk 3 h) = E (3 : Fin Nq) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_finNq_4 (E : Fin Nq -> Pauli) (h : 4 < Nq) :
    E (Fin.mk 4 h) = E (4 : Fin Nq) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_finNq_5 (E : Fin Nq -> Pauli) (h : 5 < Nq) :
    E (Fin.mk 5 h) = E (5 : Fin Nq) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_finNq_6 (E : Fin Nq -> Pauli) (h : 6 < Nq) :
    E (Fin.mk 6 h) = E (6 : Fin Nq) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_finNq_7 (E : Fin Nq -> Pauli) (h : 7 < Nq) :
    E (Fin.mk 7 h) = E (7 : Fin Nq) := by
  exact congrArg E (Fin.ext rfl)

@[simp] theorem apply_finNq_8 (E : Fin Nq -> Pauli) (h : 8 < Nq) :
    E (Fin.mk 8 h) = E (8 : Fin Nq) := by
  exact congrArg E (Fin.ext rfl)

theorem vectorParity_surfaceStabilizer (i : StabIdx) (E : Fin Nq -> Pauli) :
    vectorParity (surfaceStabilizer i) E =
      QStab.Paper.SurfaceD3CircuitDistance.parity
        (QStab.Paper.SurfaceD3CircuitDistance.stabAt i)
        (fun d => E (dataPhys d)) := by
  rw [← vectorParity_fullOfData
    (QStab.Paper.SurfaceD3CircuitDistance.stabAt i) (fun d => E (dataPhys d))]
  unfold vectorParity surfaceStabilizer fullOfData
  simp [Nq, List.finRange, dataPhys, anticommute]

theorem surfaceCentralizer_to_geo (E : DataPauli)
    (h : Centralizer surfaceSpecKnill (fullOfData E)) :
    QStab.Paper.SurfaceD3CircuitDistance.Centralizer E := by
  intro i
  have hi := h i
  simpa [surfaceSpecKnill, surfaceStabilizer, parity, vectorParity_fullOfData] using hi

theorem prodStab_surface :
    ∀ mask : Fin surfaceSpecKnill.numStab -> Bool,
      prodStab surfaceSpecKnill mask =
        fullOfData (QStab.Paper.SurfaceD3CircuitDistance.prodStab mask) := by
  intro mask
  funext q
  by_cases hq : q.val < 9
  · let q10 : Fin 10 := ⟨q.val, by omega⟩
    have h10 := congrFun (SurfaceD3.prodStab_surface mask) q10
    have hbridge :
        prodStab surfaceSpecKnill mask q =
          prodStab SurfaceD3.surfaceSpec mask q10 := by
      simp [prodStab, surfaceSpecKnill, SurfaceD3.surfaceSpec, surfaceStabilizer,
        SurfaceD3.surfaceStabilizer, fullOfData, SurfaceD3.fullOfData, hq, q10]
    rw [hbridge, h10]
    simp [fullOfData, SurfaceD3.fullOfData, hq, q10]
  · simp [prodStab, surfaceSpecKnill, surfaceStabilizer, fullOfData, hq]

theorem dataVector_fullOfData (E : DataPauli) :
    dataVector surfaceSpecKnill { paulis := fullOfData E, measFlips := fun _ => false } =
      fullOfData E := by
  funext q
  by_cases h : q.val < 9
  · simp [dataVector, surfaceSpecKnill, fullOfData, h]
  · simp [dataVector, surfaceSpecKnill, fullOfData, h]

theorem surfaceStab_to_geo (E : DataPauli)
    (h : Stab surfaceSpecKnill (fullOfData E)) :
    QStab.Paper.SurfaceD3CircuitDistance.Stab E := by
  rcases h with ⟨mask, hmask⟩
  unfold QStab.Paper.SurfaceD3CircuitDistance.Stab
  apply Finset.card_pos.mpr
  refine ⟨mask, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  funext d
  have hq := hmask (dataPhys d)
  have hprod := congrFun (prodStab_surface mask) (dataPhys d)
  rw [hprod] at hq
  simpa [fullOfData, dataPhys] using hq

theorem surfaceStab_of_geo (E : DataPauli)
    (h : QStab.Paper.SurfaceD3CircuitDistance.Stab E) :
    Stab surfaceSpecKnill (fullOfData E) := by
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
  · simp [fullOfData, hq]

theorem surfaceLogicalFailure_to_geo (es : ErrorState Nq)
    (h : logicalFailure surfaceSpecKnill es) :
    QStab.Paper.SurfaceD3CircuitDistance.LogicalAny (dataPart es) := by
  rcases h with ⟨hCent, hNotStab⟩
  constructor
  · apply surfaceCentralizer_to_geo
    simpa [dataVector_surface es] using hCent
  · intro hStab
    apply hNotStab
    have hGen := surfaceStab_of_geo (dataPart es) hStab
    simpa [dataVector_surface es] using hGen

theorem surfaceLogicalFailure_of_geo_data (es : ErrorState Nq)
    (h : QStab.Paper.SurfaceD3CircuitDistance.LogicalAny (dataPart es)) :
    logicalFailure surfaceSpecKnill es := by
  rcases h with ⟨hCent, hNotStab⟩
  constructor
  · intro i
    rw [dataVector_surface es]
    simpa [surfaceSpecKnill, surfaceStabilizer, parity, vectorParity_fullOfData] using hCent i
  · intro hStab
    apply hNotStab
    apply surfaceStab_to_geo
    simpa [dataVector_surface es] using hStab

theorem surfaceInit : surfaceBarrier (ErrorState.clean Nq) = 0 := by
  unfold surfaceBarrier SurfaceD3.surfaceBarrierData
  have hData :
      dataPart (ErrorState.clean Nq) = QStab.Paper.SurfaceD3CircuitDistance.dataI := by
    funext q
    simp [dataPart, dataPhys, QStab.Paper.SurfaceD3CircuitDistance.dataI,
      ErrorState.clean]
  rw [hData]
  simp [QStab.Paper.SurfaceD3CircuitDistance.OBL_INIT]

theorem surfaceDist :
    ∀ es, logicalFailure surfaceSpecKnill es -> surfaceSpecKnill.d <= surfaceBarrier es := by
  intro es hFail
  change 3 <= surfaceBarrier es
  unfold surfaceBarrier
  have hGeo := surfaceLogicalFailure_to_geo es hFail
  by_contra hnot
  have hlt : SurfaceD3.surfaceBarrierData (dataPart es) < 3 := by
    omega
  have hBI := SurfaceD3.BI_PAIR_surfaceBarrierData (dataPart es)
  interval_cases hf : SurfaceD3.surfaceBarrierData (dataPart es)
  · exact QStab.Paper.SurfaceD3CircuitDistance.OBL_DIST_lt3
      (dataPart es) hGeo ⟨0, by decide⟩ hBI
  · exact QStab.Paper.SurfaceD3CircuitDistance.OBL_DIST_lt3
      (dataPart es) hGeo ⟨1, by decide⟩ hBI
  · exact QStab.Paper.SurfaceD3CircuitDistance.OBL_DIST_lt3
      (dataPart es) hGeo ⟨2, by decide⟩ hBI

macro "knill_det_simp" : tactic =>
  `(tactic|
    (simp [surfaceSpecKnill, surfaceGadget, surfaceBarrier, dataPart, dataPhys,
      G0, G1, G2, G3, G4, G5, G6, G7,
      G0Slots, G1Slots, G2Slots, G3Slots, G4Slots, G5Slots, G6Slots, G7Slots,
      knillZGadget, knillXGadget, physSchedule, knillConfig, rawAncillas,
      rawAnc, raw, Nq, NumRaw, dataPhys_ne_rawAnc,
      QStab.QClifford.SurfaceD3Distance.G0Order,
      QStab.QClifford.SurfaceD3Distance.G1Order,
      QStab.QClifford.SurfaceD3Distance.G2Order,
      QStab.QClifford.SurfaceD3Distance.G3Order,
      QStab.QClifford.SurfaceD3Distance.G4Order,
      QStab.QClifford.SurfaceD3Distance.G5Order,
      QStab.QClifford.SurfaceD3Distance.G6Order,
      QStab.QClifford.SurfaceD3Distance.G7Order,
      QStab.QClifford.SurfaceD3Distance.dq,
      QStab.QClifford.Compile.compileGadget,
      QStab.QClifford.Compile.compileKnill,
      QStab.QClifford.Compile.prep0,
      QStab.QClifford.Compile.prepP,
      QStab.QClifford.Compile.cnot,
      QStab.QClifford.Compile.hadamard,
      QStab.QClifford.Compile.rawMeasZ,
      propagateCircuit, propagateGate, eraseFaults]))

set_option maxHeartbeats 2000000 in
theorem surfacePreserve :
    ∀ i, ∀ es, surfaceBarrier
        (propagateCircuit (eraseFaults (surfaceSpecKnill.gadget i)) es) = surfaceBarrier es := by
  intro i es
  fin_cases i <;>
    unfold surfaceBarrier <;>
    congr 1 <;>
    funext q <;>
    fin_cases q <;>
    knill_det_simp

def esMul (A B : ErrorState Nq) : ErrorState Nq where
  paulis := fun q => pauliMul (A.paulis q) (B.paulis q)
  measFlips := fun _ => false

theorem pauliMul_eq (a b : Pauli) : pauliMul a b = Pauli.mul a b := by
  cases a <;> cases b <;> rfl

theorem propagateGate_paulis_congr (g : Gate Nq) {A B : ErrorState Nq}
    (h : A.paulis = B.paulis) :
    (propagateGate g A).paulis = (propagateGate g B).paulis := by
  funext i
  cases g <;> simp [propagateGate, h]

theorem propagateCircuit_paulis_congr :
    ∀ (suffix : Circuit Nq) {A B : ErrorState Nq},
      A.paulis = B.paulis ->
      (propagateCircuit suffix A).paulis = (propagateCircuit suffix B).paulis
  | [], A, B, h => h
  | g :: gs, A, B, h => by
      exact propagateCircuit_paulis_congr gs (propagateGate_paulis_congr g h)

theorem propagateGate_paulis_esMul (g : Gate Nq) (A B : ErrorState Nq) :
    (propagateGate g (esMul A B)).paulis =
      (esMul (propagateGate g A) (propagateGate g B)).paulis := by
  funext i
  cases g with
  | prepZero q =>
      by_cases h : i = q <;> simp [propagateGate, esMul, h]
  | prepPlus q =>
      by_cases h : i = q <;> simp [propagateGate, esMul, h]
  | hadamard q =>
      by_cases h : i = q
      · simp [propagateGate, esMul, h]
        cases A.paulis q <;> cases B.paulis q <;> rfl
      · simp [propagateGate, esMul, h]
  | measZ q =>
      simp [propagateGate, esMul]
  | cnot c t hne =>
      by_cases ht : i = t
      · simp [propagateGate, esMul, ht]
        cases A.paulis c <;> cases A.paulis t <;>
          cases B.paulis c <;> cases B.paulis t <;> rfl
      · by_cases hc : i = c
        · have hct : c ≠ t := hne
          simp [propagateGate, esMul, hc, hct]
          cases A.paulis c <;> cases A.paulis t <;>
            cases B.paulis c <;> cases B.paulis t <;> rfl
        · simp [propagateGate, esMul, ht, hc]

theorem propagateCircuit_paulis_esMul :
    ∀ (suffix : Circuit Nq) (A B : ErrorState Nq),
      (propagateCircuit suffix (esMul A B)).paulis =
        (esMul (propagateCircuit suffix A) (propagateCircuit suffix B)).paulis
  | [], A, B => rfl
  | g :: gs, A, B => by
      have hstart := propagateGate_paulis_esMul g A B
      have hcongr := propagateCircuit_paulis_congr gs hstart
      exact hcongr.trans (propagateCircuit_paulis_esMul gs (propagateGate g A) (propagateGate g B))

def singleError (q : Fin Nq) (p : Pauli) : ErrorState Nq :=
  (ErrorState.clean Nq).inject q p

theorem inject_paulis_eq_esMul_single (es : ErrorState Nq) (q : Fin Nq) (p : Pauli) :
    (es.inject q p).paulis = (esMul (singleError q p) es).paulis := by
  funext i
  by_cases h : i = q
  · subst h
    simp [ErrorState.inject, singleError, esMul, ErrorState.clean, pauliMul_eq]
    cases p <;> cases es.paulis i <;> rfl
  · simp [ErrorState.inject, singleError, esMul, ErrorState.clean, h, pauliMul_eq]
    cases es.paulis i <;> rfl

def qFaultDelta (q : Fin Nq) (suffix : Circuit Nq) (p : Pauli) : DataPauli :=
  dataPart (propagateCircuit suffix (singleError q p))

def QSiteSafe (q : Fin Nq) (suffix : Circuit Nq) : Prop :=
  ∀ p, p ≠ Pauli.I ->
    QStab.Paper.SurfaceD3CircuitDistance.DeltaSafeFast (qFaultDelta q suffix p)

theorem dataPart_propagate_inject (suffix : Circuit Nq)
    (es : ErrorState Nq) (q : Fin Nq) (p : Pauli) :
    dataPart (propagateCircuit suffix (es.inject q p)) =
      QStab.Paper.SurfaceD3CircuitDistance.pmul
        (dataPart (propagateCircuit suffix es))
        (qFaultDelta q suffix p) := by
  have hInject := inject_paulis_eq_esMul_single es q p
  have hCong := propagateCircuit_paulis_congr suffix hInject
  have hMul := propagateCircuit_paulis_esMul suffix (singleError q p) es
  funext d
  have hpoint := congrFun (hCong.trans hMul) (dataPhys d)
  change (propagateCircuit suffix (es.inject q p)).paulis (dataPhys d) =
    Pauli.mul ((propagateCircuit suffix es).paulis (dataPhys d))
      ((propagateCircuit suffix (singleError q p)).paulis (dataPhys d))
  rw [hpoint]
  simp [esMul, pauliMul_eq]
  cases (propagateCircuit suffix (singleError q p)).paulis (dataPhys d) <;>
    cases (propagateCircuit suffix es).paulis (dataPhys d) <;> rfl

instance instDecidableQSiteSafe (q : Fin Nq) (suffix : Circuit Nq) :
    Decidable (QSiteSafe q suffix) := by
  unfold QSiteSafe
  infer_instance

theorem surfaceBarrierData_step {E D : DataPauli}
    (hD : QStab.Paper.SurfaceD3CircuitDistance.DeltaSafe D) :
    SurfaceD3.surfaceBarrierData (QStab.Paper.SurfaceD3CircuitDistance.pmul E D) <=
      SurfaceD3.surfaceBarrierData E + 1 := by
  apply SurfaceD3.surfaceBarrierData_le_of_BI_PAIR
  exact QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR_pmul_of_delta_safe
    (SurfaceD3.BI_PAIR_surfaceBarrierData E) hD

theorem surfaceSiteSafe_of_QSiteSafe {q : Fin Nq} {suffix : Circuit Nq}
    (hSafe : QSiteSafe q suffix) :
    SiteSafeBeta surfaceBarrier ⟨q, suffix⟩ := by
  intro es p hp
  unfold surfaceBarrier
  rw [dataPart_propagate_inject suffix es q p]
  exact surfaceBarrierData_step (QStab.Paper.SurfaceD3CircuitDistance.DeltaSafe_of_fast (hSafe p hp))

def AllSitesSafe : FCircuit Nq -> Prop
  | [] => True
  | .gate _ :: rest => AllSitesSafe rest
  | .errLoc q :: rest => QSiteSafe q (eraseFaults rest) ∧ AllSitesSafe rest

instance instDecidableAllSitesSafe : (fc : FCircuit Nq) -> Decidable (AllSitesSafe fc)
  | [] => isTrue trivial
  | .gate _ :: rest => instDecidableAllSitesSafe rest
  | .errLoc q :: rest =>
      match instDecidableQSiteSafe q (eraseFaults rest), instDecidableAllSitesSafe rest with
      | isTrue hq, isTrue hr => isTrue ⟨hq, hr⟩
      | isFalse hnq, _ => isFalse (fun h => hnq h.1)
      | _, isFalse hnr => isFalse (fun h => hnr h.2)

theorem allSitesSafe_G0 : AllSitesSafe G0 := by
  simp [G0, knillZGadget, physSchedule, knillConfig, rawAncillas, rawAnc, raw,
    dataPhys, G0Slots, QStab.QClifford.SurfaceD3Distance.G0Order,
    QStab.QClifford.SurfaceD3Distance.dq,
    QStab.QClifford.Compile.compileGadget,
    QStab.QClifford.Compile.compileKnill, QStab.QClifford.Compile.prep0,
    QStab.QClifford.Compile.cnot, QStab.QClifford.Compile.rawMeasZ,
    AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem allSitesSafe_G1 : AllSitesSafe G1 := by
  simp [G1, knillXGadget, physSchedule, knillConfig, rawAncillas, rawAnc, raw,
    dataPhys, G1Slots, QStab.QClifford.SurfaceD3Distance.G1Order,
    QStab.QClifford.SurfaceD3Distance.dq,
    QStab.QClifford.Compile.compileGadget,
    QStab.QClifford.Compile.compileKnill, QStab.QClifford.Compile.prepP,
    QStab.QClifford.Compile.cnot, QStab.QClifford.Compile.hadamard,
    QStab.QClifford.Compile.rawMeasZ, AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem allSitesSafe_G2 : AllSitesSafe G2 := by
  simp [G2, knillXGadget, physSchedule, knillConfig, rawAncillas, rawAnc, raw,
    dataPhys, G2Slots, QStab.QClifford.SurfaceD3Distance.G2Order,
    QStab.QClifford.SurfaceD3Distance.dq,
    QStab.QClifford.Compile.compileGadget,
    QStab.QClifford.Compile.compileKnill, QStab.QClifford.Compile.prepP,
    QStab.QClifford.Compile.cnot, QStab.QClifford.Compile.hadamard,
    QStab.QClifford.Compile.rawMeasZ, AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem allSitesSafe_G3 : AllSitesSafe G3 := by
  simp [G3, knillZGadget, physSchedule, knillConfig, rawAncillas, rawAnc, raw,
    dataPhys, G3Slots, QStab.QClifford.SurfaceD3Distance.G3Order,
    QStab.QClifford.SurfaceD3Distance.dq,
    QStab.QClifford.Compile.compileGadget,
    QStab.QClifford.Compile.compileKnill, QStab.QClifford.Compile.prep0,
    QStab.QClifford.Compile.cnot, QStab.QClifford.Compile.rawMeasZ,
    AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem allSitesSafe_G4 : AllSitesSafe G4 := by
  simp [G4, knillXGadget, physSchedule, knillConfig, rawAncillas, rawAnc, raw,
    dataPhys, G4Slots, QStab.QClifford.SurfaceD3Distance.G4Order,
    QStab.QClifford.SurfaceD3Distance.dq,
    QStab.QClifford.Compile.compileGadget,
    QStab.QClifford.Compile.compileKnill, QStab.QClifford.Compile.prepP,
    QStab.QClifford.Compile.cnot, QStab.QClifford.Compile.hadamard,
    QStab.QClifford.Compile.rawMeasZ, AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem allSitesSafe_G5 : AllSitesSafe G5 := by
  simp [G5, knillZGadget, physSchedule, knillConfig, rawAncillas, rawAnc, raw,
    dataPhys, G5Slots, QStab.QClifford.SurfaceD3Distance.G5Order,
    QStab.QClifford.SurfaceD3Distance.dq,
    QStab.QClifford.Compile.compileGadget,
    QStab.QClifford.Compile.compileKnill, QStab.QClifford.Compile.prep0,
    QStab.QClifford.Compile.cnot, QStab.QClifford.Compile.rawMeasZ,
    AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem allSitesSafe_G6 : AllSitesSafe G6 := by
  simp [G6, knillZGadget, physSchedule, knillConfig, rawAncillas, rawAnc, raw,
    dataPhys, G6Slots, QStab.QClifford.SurfaceD3Distance.G6Order,
    QStab.QClifford.SurfaceD3Distance.dq,
    QStab.QClifford.Compile.compileGadget,
    QStab.QClifford.Compile.compileKnill, QStab.QClifford.Compile.prep0,
    QStab.QClifford.Compile.cnot, QStab.QClifford.Compile.rawMeasZ,
    AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem allSitesSafe_G7 : AllSitesSafe G7 := by
  simp [G7, knillXGadget, physSchedule, knillConfig, rawAncillas, rawAnc, raw,
    dataPhys, G7Slots, QStab.QClifford.SurfaceD3Distance.G7Order,
    QStab.QClifford.SurfaceD3Distance.dq,
    QStab.QClifford.Compile.compileGadget,
    QStab.QClifford.Compile.compileKnill, QStab.QClifford.Compile.prepP,
    QStab.QClifford.Compile.cnot, QStab.QClifford.Compile.hadamard,
    QStab.QClifford.Compile.rawMeasZ, AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem surfaceStep_of_allSitesSafe :
    ∀ fc : FCircuit Nq,
      AllSitesSafe fc ->
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
    ∀ i, ∀ site, site ∈ errLocsWithSuffix (surfaceSpecKnill.gadget i) ->
      SiteSafeBeta surfaceBarrier site := by
  intro i
  fin_cases i
  · change ∀ site, site ∈ errLocsWithSuffix G0 -> SiteSafeBeta surfaceBarrier site
    exact surfaceStep_of_allSitesSafe G0 allSitesSafe_G0
  · change ∀ site, site ∈ errLocsWithSuffix G1 -> SiteSafeBeta surfaceBarrier site
    exact surfaceStep_of_allSitesSafe G1 allSitesSafe_G1
  · change ∀ site, site ∈ errLocsWithSuffix G2 -> SiteSafeBeta surfaceBarrier site
    exact surfaceStep_of_allSitesSafe G2 allSitesSafe_G2
  · change ∀ site, site ∈ errLocsWithSuffix G3 -> SiteSafeBeta surfaceBarrier site
    exact surfaceStep_of_allSitesSafe G3 allSitesSafe_G3
  · change ∀ site, site ∈ errLocsWithSuffix G4 -> SiteSafeBeta surfaceBarrier site
    exact surfaceStep_of_allSitesSafe G4 allSitesSafe_G4
  · change ∀ site, site ∈ errLocsWithSuffix G5 -> SiteSafeBeta surfaceBarrier site
    exact surfaceStep_of_allSitesSafe G5 allSitesSafe_G5
  · change ∀ site, site ∈ errLocsWithSuffix G6 -> SiteSafeBeta surfaceBarrier site
    exact surfaceStep_of_allSitesSafe G6 allSitesSafe_G6
  · change ∀ site, site ∈ errLocsWithSuffix G7 -> SiteSafeBeta surfaceBarrier site
    exact surfaceStep_of_allSitesSafe G7 allSitesSafe_G7

theorem surfaceParity0 (E : Fin Nq -> Pauli) :
    vectorParity (surfaceStabilizer (0 : StabIdx)) E =
      (anticommute Pauli.Z (E (0 : Fin Nq)) ^^
        (anticommute Pauli.Z (E (1 : Fin Nq)) ^^
          (anticommute Pauli.Z (E (3 : Fin Nq)) ^^
            anticommute Pauli.Z (E (4 : Fin Nq))))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s0,
    ← SurfaceD3.anticommute_eq_paper, anticommute, dataPhys]

theorem surfaceParity1 (E : Fin Nq -> Pauli) :
    vectorParity (surfaceStabilizer (1 : StabIdx)) E =
      (anticommute Pauli.X (E (1 : Fin Nq)) ^^
        (anticommute Pauli.X (E (2 : Fin Nq)) ^^
          (anticommute Pauli.X (E (4 : Fin Nq)) ^^
            anticommute Pauli.X (E (5 : Fin Nq))))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s1,
    ← SurfaceD3.anticommute_eq_paper, anticommute, dataPhys]

theorem surfaceParity2 (E : Fin Nq -> Pauli) :
    vectorParity (surfaceStabilizer (2 : StabIdx)) E =
      (anticommute Pauli.X (E (3 : Fin Nq)) ^^
        (anticommute Pauli.X (E (4 : Fin Nq)) ^^
          (anticommute Pauli.X (E (6 : Fin Nq)) ^^
            anticommute Pauli.X (E (7 : Fin Nq))))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s2,
    ← SurfaceD3.anticommute_eq_paper, anticommute, dataPhys]

theorem surfaceParity3 (E : Fin Nq -> Pauli) :
    vectorParity (surfaceStabilizer (3 : StabIdx)) E =
      (anticommute Pauli.Z (E (4 : Fin Nq)) ^^
        (anticommute Pauli.Z (E (5 : Fin Nq)) ^^
          (anticommute Pauli.Z (E (7 : Fin Nq)) ^^
            anticommute Pauli.Z (E (8 : Fin Nq))))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s3,
    ← SurfaceD3.anticommute_eq_paper, anticommute, dataPhys]

theorem surfaceParity4 (E : Fin Nq -> Pauli) :
    vectorParity (surfaceStabilizer (4 : StabIdx)) E =
      (anticommute Pauli.X (E (0 : Fin Nq)) ^^
        anticommute Pauli.X (E (1 : Fin Nq))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s4,
    ← SurfaceD3.anticommute_eq_paper, anticommute, dataPhys]

theorem surfaceParity5 (E : Fin Nq -> Pauli) :
    vectorParity (surfaceStabilizer (5 : StabIdx)) E =
      (anticommute Pauli.Z (E (2 : Fin Nq)) ^^
        anticommute Pauli.Z (E (5 : Fin Nq))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s5,
    ← SurfaceD3.anticommute_eq_paper, anticommute, dataPhys]

theorem surfaceParity6 (E : Fin Nq -> Pauli) :
    vectorParity (surfaceStabilizer (6 : StabIdx)) E =
      (anticommute Pauli.Z (E (3 : Fin Nq)) ^^
        anticommute Pauli.Z (E (6 : Fin Nq))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s6,
    ← SurfaceD3.anticommute_eq_paper, anticommute, dataPhys]

theorem surfaceParity7 (E : Fin Nq -> Pauli) :
    vectorParity (surfaceStabilizer (7 : StabIdx)) E =
      (anticommute Pauli.X (E (7 : Fin Nq)) ^^
        anticommute Pauli.X (E (8 : Fin Nq))) := by
  rw [vectorParity_surfaceStabilizer]
  simp [QStab.Paper.SurfaceD3CircuitDistance.parity,
    QStab.Paper.SurfaceD3CircuitDistance.stabAt,
    QStab.Paper.SurfaceD3CircuitDistance.s7,
    ← SurfaceD3.anticommute_eq_paper, anticommute, dataPhys]

@[simp] theorem hasXComp_xPart_eq_anticommute_Z (p : Pauli) :
    hasXComp (xPart p) = anticommute Pauli.Z p := by
  cases p <;> rfl

@[simp] theorem hasXComp_hadamard_zPart_eq_anticommute_X (p : Pauli) :
    hasXComp (hadamardAction (zPart p)) = anticommute Pauli.X p := by
  cases p <;> rfl

theorem xor_swap_mid (a b c : Bool) : xor a (xor b c) = xor b (xor a c) := by
  cases a <;> cases b <;> cases c <;> rfl

macro "knill_syn_unfold_g0" : tactic =>
  `(tactic|
    (unfold syndromeBit xorBools surfaceSpecKnill
      stateOfPauliAtDetector readout
      G0 G0Slots
      knillZGadget physSchedule knillConfig rawAncillas rawAnc raw dataPhys
      QStab.QClifford.Compile.compileGadget
      QStab.QClifford.Compile.compileKnill
      QStab.QClifford.Compile.prep0
      QStab.QClifford.Compile.prepP
      QStab.QClifford.Compile.cnot
      QStab.QClifford.Compile.hadamard
      QStab.QClifford.Compile.rawMeasZ
      QStab.QClifford.SurfaceD3Distance.G0Order
      QStab.QClifford.SurfaceD3Distance.dq
     simp [Nq, NumRaw, List.finRange, propagateCircuit, propagateGate, eraseFaults]))

macro "knill_syn_unfold_g1" : tactic =>
  `(tactic|
    (unfold syndromeBit xorBools surfaceSpecKnill
      stateOfPauliAtDetector readout
      G1 G1Slots
      knillXGadget physSchedule knillConfig rawAncillas rawAnc raw dataPhys
      QStab.QClifford.Compile.compileGadget
      QStab.QClifford.Compile.compileKnill
      QStab.QClifford.Compile.prep0
      QStab.QClifford.Compile.prepP
      QStab.QClifford.Compile.cnot
      QStab.QClifford.Compile.hadamard
      QStab.QClifford.Compile.rawMeasZ
      QStab.QClifford.SurfaceD3Distance.G1Order
      QStab.QClifford.SurfaceD3Distance.dq
     simp [Nq, NumRaw, List.finRange, propagateCircuit, propagateGate, eraseFaults]))

macro "knill_syn_unfold_g2" : tactic =>
  `(tactic|
    (unfold syndromeBit xorBools surfaceSpecKnill
      stateOfPauliAtDetector readout
      G2 G2Slots
      knillXGadget physSchedule knillConfig rawAncillas rawAnc raw dataPhys
      QStab.QClifford.Compile.compileGadget
      QStab.QClifford.Compile.compileKnill
      QStab.QClifford.Compile.prep0
      QStab.QClifford.Compile.prepP
      QStab.QClifford.Compile.cnot
      QStab.QClifford.Compile.hadamard
      QStab.QClifford.Compile.rawMeasZ
      QStab.QClifford.SurfaceD3Distance.G2Order
      QStab.QClifford.SurfaceD3Distance.dq
     simp [Nq, NumRaw, List.finRange, propagateCircuit, propagateGate, eraseFaults]))

macro "knill_syn_unfold_g3" : tactic =>
  `(tactic|
    (unfold syndromeBit xorBools surfaceSpecKnill
      stateOfPauliAtDetector readout
      G3 G3Slots
      knillZGadget physSchedule knillConfig rawAncillas rawAnc raw dataPhys
      QStab.QClifford.Compile.compileGadget
      QStab.QClifford.Compile.compileKnill
      QStab.QClifford.Compile.prep0
      QStab.QClifford.Compile.prepP
      QStab.QClifford.Compile.cnot
      QStab.QClifford.Compile.hadamard
      QStab.QClifford.Compile.rawMeasZ
      QStab.QClifford.SurfaceD3Distance.G3Order
      QStab.QClifford.SurfaceD3Distance.dq
     simp [Nq, NumRaw, List.finRange, propagateCircuit, propagateGate, eraseFaults]))

macro "knill_syn_unfold_g4" : tactic =>
  `(tactic|
    (unfold syndromeBit xorBools surfaceSpecKnill
      stateOfPauliAtDetector readout
      G4 G4Slots
      knillXGadget physSchedule knillConfig rawAncillas rawAnc raw dataPhys
      QStab.QClifford.Compile.compileGadget
      QStab.QClifford.Compile.compileKnill
      QStab.QClifford.Compile.prep0
      QStab.QClifford.Compile.prepP
      QStab.QClifford.Compile.cnot
      QStab.QClifford.Compile.hadamard
      QStab.QClifford.Compile.rawMeasZ
      QStab.QClifford.SurfaceD3Distance.G4Order
      QStab.QClifford.SurfaceD3Distance.dq
     simp [Nq, NumRaw, List.finRange, propagateCircuit, propagateGate, eraseFaults]))

macro "knill_syn_unfold_g5" : tactic =>
  `(tactic|
    (unfold syndromeBit xorBools surfaceSpecKnill
      stateOfPauliAtDetector readout
      G5 G5Slots
      knillZGadget physSchedule knillConfig rawAncillas rawAnc raw dataPhys
      QStab.QClifford.Compile.compileGadget
      QStab.QClifford.Compile.compileKnill
      QStab.QClifford.Compile.prep0
      QStab.QClifford.Compile.prepP
      QStab.QClifford.Compile.cnot
      QStab.QClifford.Compile.hadamard
      QStab.QClifford.Compile.rawMeasZ
      QStab.QClifford.SurfaceD3Distance.G5Order
      QStab.QClifford.SurfaceD3Distance.dq
     simp [Nq, NumRaw, List.finRange, propagateCircuit, propagateGate, eraseFaults]))

macro "knill_syn_unfold_g6" : tactic =>
  `(tactic|
    (unfold syndromeBit xorBools surfaceSpecKnill
      stateOfPauliAtDetector readout
      G6 G6Slots
      knillZGadget physSchedule knillConfig rawAncillas rawAnc raw dataPhys
      QStab.QClifford.Compile.compileGadget
      QStab.QClifford.Compile.compileKnill
      QStab.QClifford.Compile.prep0
      QStab.QClifford.Compile.prepP
      QStab.QClifford.Compile.cnot
      QStab.QClifford.Compile.hadamard
      QStab.QClifford.Compile.rawMeasZ
      QStab.QClifford.SurfaceD3Distance.G6Order
      QStab.QClifford.SurfaceD3Distance.dq
     simp [Nq, NumRaw, List.finRange, propagateCircuit, propagateGate, eraseFaults]))

macro "knill_syn_unfold_g7" : tactic =>
  `(tactic|
    (unfold syndromeBit xorBools surfaceSpecKnill
      stateOfPauliAtDetector readout
      G7 G7Slots
      knillXGadget physSchedule knillConfig rawAncillas rawAnc raw dataPhys
      QStab.QClifford.Compile.compileGadget
      QStab.QClifford.Compile.compileKnill
      QStab.QClifford.Compile.prep0
      QStab.QClifford.Compile.prepP
      QStab.QClifford.Compile.cnot
      QStab.QClifford.Compile.hadamard
      QStab.QClifford.Compile.rawMeasZ
      QStab.QClifford.SurfaceD3Distance.G7Order
      QStab.QClifford.SurfaceD3Distance.dq
     simp [Nq, NumRaw, List.finRange, propagateCircuit, propagateGate, eraseFaults]))

set_option maxHeartbeats 4000000 in
theorem surfaceSyn :
    ∀ i E,
      gadgetMeasFlip knillSurfaceCircuit surfaceSpecKnill i E =
        parity surfaceSpecKnill (surfaceSpecKnill.stabilizer i) E := by
  intro i E
  fin_cases i
  · change syndromeBit surfaceSpecKnill
      (propagateCircuit (eraseFaults G0) (stateOfPauliAtDetector 0 E))
        (⟨0, by decide⟩ : Fin surfaceSpecKnill.numStab) =
      vectorParity (surfaceStabilizer (0 : StabIdx)) E
    rw [surfaceParity0]
    knill_syn_unfold_g0
    exact xor_swap_mid _ _ _
  · change syndromeBit surfaceSpecKnill
      (propagateCircuit (eraseFaults G1) (stateOfPauliAtDetector 4 E))
        (⟨1, by decide⟩ : Fin surfaceSpecKnill.numStab) =
      vectorParity (surfaceStabilizer (1 : StabIdx)) E
    rw [surfaceParity1]
    knill_syn_unfold_g1
  · change syndromeBit surfaceSpecKnill
      (propagateCircuit (eraseFaults G2) (stateOfPauliAtDetector 8 E))
        (⟨2, by decide⟩ : Fin surfaceSpecKnill.numStab) =
      vectorParity (surfaceStabilizer (2 : StabIdx)) E
    rw [surfaceParity2]
    knill_syn_unfold_g2
  · change syndromeBit surfaceSpecKnill
      (propagateCircuit (eraseFaults G3) (stateOfPauliAtDetector 12 E))
        (⟨3, by decide⟩ : Fin surfaceSpecKnill.numStab) =
      vectorParity (surfaceStabilizer (3 : StabIdx)) E
    rw [surfaceParity3]
    knill_syn_unfold_g3
    exact xor_swap_mid _ _ _
  · change syndromeBit surfaceSpecKnill
      (propagateCircuit (eraseFaults G4) (stateOfPauliAtDetector 16 E))
        (⟨4, by decide⟩ : Fin surfaceSpecKnill.numStab) =
      vectorParity (surfaceStabilizer (4 : StabIdx)) E
    rw [surfaceParity4]
    knill_syn_unfold_g4
  · change syndromeBit surfaceSpecKnill
      (propagateCircuit (eraseFaults G5) (stateOfPauliAtDetector 18 E))
        (⟨5, by decide⟩ : Fin surfaceSpecKnill.numStab) =
      vectorParity (surfaceStabilizer (5 : StabIdx)) E
    rw [surfaceParity5]
    knill_syn_unfold_g5
  · change syndromeBit surfaceSpecKnill
      (propagateCircuit (eraseFaults G6) (stateOfPauliAtDetector 20 E))
        (⟨6, by decide⟩ : Fin surfaceSpecKnill.numStab) =
      vectorParity (surfaceStabilizer (6 : StabIdx)) E
    rw [surfaceParity6]
    knill_syn_unfold_g6
  · change syndromeBit surfaceSpecKnill
      (propagateCircuit (eraseFaults G7) (stateOfPauliAtDetector 22 E))
        (⟨7, by decide⟩ : Fin surfaceSpecKnill.numStab) =
      vectorParity (surfaceStabilizer (7 : StabIdx)) E
    rw [surfaceParity7]
    knill_syn_unfold_g7

theorem surfaceProgramEq :
    knillSurfaceCircuit = specCircuit surfaceSpecKnill := by
  simp [specCircuit, surfaceSpecKnill, surfaceGadget, knillSurfaceCircuit,
    List.finRange]

theorem surfaceWF : WellFormed knillSurfaceCircuit surfaceSpecKnill := by
  rfl

def reachLogicalXScript : List (Option Pauli) :=
  (List.range 49).map fun i =>
    if i = 1 ∨ i = 5 ∨ i = 48 then some Pauli.X else none

set_option maxHeartbeats 8000000 in
theorem surfaceReachScript_faults :
    (runFScript knillSurfaceCircuit reachLogicalXScript
      (ErrorState.clean Nq)).2 = surfaceSpecKnill.d := by
  unfold surfaceSpecKnill knillSurfaceCircuit G0 G1 G2 G3 G4 G5 G6 G7
    knillZGadget knillXGadget physSchedule knillConfig rawAncillas rawAnc
    G0Slots G1Slots G2Slots G3Slots G4Slots G5Slots G6Slots G7Slots
    QStab.QClifford.Compile.compileGadget
    QStab.QClifford.Compile.compileKnill
    QStab.QClifford.Compile.prep0
    QStab.QClifford.Compile.prepP
    QStab.QClifford.Compile.cnot
    QStab.QClifford.Compile.hadamard
    QStab.QClifford.Compile.rawMeasZ
    QStab.QClifford.SurfaceD3Distance.G0Order
    QStab.QClifford.SurfaceD3Distance.G1Order
    QStab.QClifford.SurfaceD3Distance.G2Order
    QStab.QClifford.SurfaceD3Distance.G3Order
    QStab.QClifford.SurfaceD3Distance.G4Order
    QStab.QClifford.SurfaceD3Distance.G5Order
    QStab.QClifford.SurfaceD3Distance.G6Order
    QStab.QClifford.SurfaceD3Distance.G7Order
    reachLogicalXScript runFScript
  decide

set_option maxHeartbeats 8000000 in
theorem surfaceReachScript_data :
    dataPart
      (runFScript knillSurfaceCircuit reachLogicalXScript
        (ErrorState.clean Nq)).1 =
      QStab.Paper.SurfaceD3CircuitDistance.logicalX := by
  funext q
  fin_cases q <;>
    unfold knillSurfaceCircuit G0 G1 G2 G3 G4 G5 G6 G7
      knillZGadget knillXGadget physSchedule knillConfig rawAncillas rawAnc
      G0Slots G1Slots G2Slots G3Slots G4Slots G5Slots G6Slots G7Slots
      QStab.QClifford.Compile.compileGadget
      QStab.QClifford.Compile.compileKnill
      QStab.QClifford.Compile.prep0
      QStab.QClifford.Compile.prepP
      QStab.QClifford.Compile.cnot
      QStab.QClifford.Compile.hadamard
      QStab.QClifford.Compile.rawMeasZ
      QStab.QClifford.SurfaceD3Distance.G0Order
      QStab.QClifford.SurfaceD3Distance.G1Order
      QStab.QClifford.SurfaceD3Distance.G2Order
      QStab.QClifford.SurfaceD3Distance.G3Order
      QStab.QClifford.SurfaceD3Distance.G4Order
      QStab.QClifford.SurfaceD3Distance.G5Order
      QStab.QClifford.SurfaceD3Distance.G6Order
      QStab.QClifford.SurfaceD3Distance.G7Order
      reachLogicalXScript runFScript dataPart dataPhys <;>
    decide

set_option maxHeartbeats 8000000 in
theorem surfaceReachScript_undetected :
    undetected surfaceSpecKnill
      (runFScript knillSurfaceCircuit reachLogicalXScript
        (ErrorState.clean Nq)).1 := by
  intro i
  fin_cases i <;>
    unfold syndromeBit xorBools surfaceSpecKnill readout knillSurfaceCircuit
      G0 G1 G2 G3 G4 G5 G6 G7
      knillZGadget knillXGadget physSchedule knillConfig rawAncillas rawAnc
      G0Slots G1Slots G2Slots G3Slots G4Slots G5Slots G6Slots G7Slots
      QStab.QClifford.Compile.compileGadget
      QStab.QClifford.Compile.compileKnill
      QStab.QClifford.Compile.prep0
      QStab.QClifford.Compile.prepP
      QStab.QClifford.Compile.cnot
      QStab.QClifford.Compile.hadamard
      QStab.QClifford.Compile.rawMeasZ
      QStab.QClifford.SurfaceD3Distance.G0Order
      QStab.QClifford.SurfaceD3Distance.G1Order
      QStab.QClifford.SurfaceD3Distance.G2Order
      QStab.QClifford.SurfaceD3Distance.G3Order
      QStab.QClifford.SurfaceD3Distance.G4Order
      QStab.QClifford.SurfaceD3Distance.G5Order
      QStab.QClifford.SurfaceD3Distance.G6Order
      QStab.QClifford.SurfaceD3Distance.G7Order
      reachLogicalXScript runFScript <;>
    decide

theorem surfaceReachOk :
    (runFScript knillSurfaceCircuit reachLogicalXScript
      (ErrorState.clean Nq)).2 = surfaceSpecKnill.d ∧
      failure surfaceSpecKnill
        (runFScript knillSurfaceCircuit reachLogicalXScript
          (ErrorState.clean Nq)).1 := by
  constructor
  · exact surfaceReachScript_faults
  · constructor
    · apply surfaceLogicalFailure_of_geo_data
      have hData := surfaceReachScript_data
      simpa [hData] using QStab.Paper.SurfaceD3CircuitDistance.logicalX_real
    · constructor
      · exact surfaceReachScript_undetected
      · intro i hi
        simp [surfaceSpecKnill] at hi

def knillCert :
    DistanceCertificate knillSurfaceCircuit surfaceSpecKnill where
  barrier := surfaceBarrier
  programEq := surfaceProgramEq
  wf := surfaceWF
  syn := surfaceSyn
  init := surfaceInit
  step := surfaceStep
  preserve := surfacePreserve
  dist := surfaceDist
  reachScript := reachLogicalXScript
  reachOk := surfaceReachOk

def surfaceD3KnillInput : VCInput Nq :=
  VCInput.ofPCC knillSurfaceCircuit surfaceSpecKnill
    .unconditional (by decide) (by decide)

def surfaceD3KnillVCGen : VCGen surfaceD3KnillInput :=
  VCGen.ofDistanceCertificate knillCert (by decide) (by decide)

theorem surfaceD3_knill_safe_vcgen :
    Safe knillSurfaceCircuit surfaceSpecKnill := by
  simpa [surfaceD3KnillInput] using vcgen_sound surfaceD3KnillVCGen

theorem surfaceD3_knill_safe :
    Safe knillSurfaceCircuit surfaceSpecKnill :=
  surfaceD3_knill_safe_vcgen

#print axioms surfaceD3_knill_safe

end QStab.QClifford.PCC.SurfaceD3Knill
