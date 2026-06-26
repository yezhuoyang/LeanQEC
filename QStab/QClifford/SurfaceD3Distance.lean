import QStab.QClifford.FaultHoare
import QStab.QClifford.PropagateLemmas
import QStab.Paper.SurfaceD3CircuitDistance

/-!
# Surface-d3 NZ distance at QClifford

This is the authoritative QClifford-level derivation for the concrete
surface-d3 NZ syndrome-extraction circuit.  The Hoare derivation is a
`QStab.QClifford.FDeriv`, so its soundness is the audited QClifford
`fhoare_sound` theorem over `qceval`.

The finite surface-code geometry (`BI_PAIR`, `LogicalAny`, stabilizer
arithmetic) is reused from the paper kernel file.  The circuit, fault
locations, propagation, fault counter, Hoare derivation, and reachability
witness are all QClifford objects.
-/

namespace QStab.QClifford.SurfaceD3Distance

abbrev DataQ := QStab.Paper.SurfaceD3CircuitDistance.DataQ
abbrev DataPauli := QStab.Paper.SurfaceD3CircuitDistance.DataPauli
abbrev StabIdx := QStab.Paper.SurfaceD3CircuitDistance.StabIdx

def qq (n : Nat) (h : n < 10 := by decide) : Fin 10 := ⟨n, h⟩
def dq (n : Nat) (h : n < 9 := by decide) : DataQ := ⟨n, h⟩

def physOfData (q : DataQ) : Fin 10 := ⟨q.val, by omega⟩

theorem physOfData_ne_anc (q : DataQ) : physOfData q ≠ qq 9 := by
  intro h
  have hv := congrArg Fin.val h
  simp [physOfData, qq] at hv
  omega

def cnot (c t : Nat) (hc : c < 10 := by decide) (ht : t < 10 := by decide)
    (hne : (⟨c, hc⟩ : Fin 10) ≠ ⟨t, ht⟩ := by decide) : Gate 10 :=
  Gate.cnot ⟨c, hc⟩ ⟨t, ht⟩ hne

def zGadget (order : List DataQ) : FCircuit 10 :=
  [.errLoc (qq 9), .gate (.prepZero (qq 9))] ++
  (order.map (fun q =>
    let qp := physOfData q
    [.errLoc qp, .errLoc (qq 9), .gate (.cnot qp (qq 9) (physOfData_ne_anc q))])).flatten ++
  [.errLoc (qq 9), .gate (.measZ (qq 9))]

def xGadget (order : List DataQ) : FCircuit 10 :=
  [.errLoc (qq 9), .gate (.prepPlus (qq 9))] ++
  (order.map (fun q =>
    let qp := physOfData q
    [.errLoc (qq 9), .errLoc qp,
      .gate (.cnot (qq 9) qp (Ne.symm (physOfData_ne_anc q)))])).flatten ++
  [.errLoc (qq 9), .gate (.hadamard (qq 9)), .errLoc (qq 9), .gate (.measZ (qq 9))]

def G0Order : List DataQ := [dq 0, dq 3, dq 1, dq 4]
def G1Order : List DataQ := [dq 1, dq 2, dq 4, dq 5]
def G2Order : List DataQ := [dq 3, dq 4, dq 6, dq 7]
def G3Order : List DataQ := [dq 4, dq 7, dq 5, dq 8]
def G4Order : List DataQ := [dq 0, dq 1]
def G5Order : List DataQ := [dq 2, dq 5]
def G6Order : List DataQ := [dq 3, dq 6]
def G7Order : List DataQ := [dq 7, dq 8]

def G0 : FCircuit 10 := zGadget G0Order
def G1 : FCircuit 10 := xGadget G1Order
def G2 : FCircuit 10 := xGadget G2Order
def G3 : FCircuit 10 := zGadget G3Order
def G4 : FCircuit 10 := xGadget G4Order
def G5 : FCircuit 10 := zGadget G5Order
def G6 : FCircuit 10 := zGadget G6Order
def G7 : FCircuit 10 := xGadget G7Order

def C_NZ_D3 : FCircuit 10 :=
  G0 ++ (G1 ++ (G2 ++ (G3 ++ (G4 ++ (G5 ++ (G6 ++ G7))))))

def distanceBound : Nat := 3

def dataPart (es : ErrorState 10) : DataPauli :=
  fun q => es.paulis ⟨q.val, by omega⟩

def anc : Fin 10 := qq 9

theorem physOfData_ne_anc' (q : DataQ) : physOfData q ≠ anc := by
  simpa [anc] using physOfData_ne_anc q

theorem dataPhys_ne_anc (q : DataQ) : (⟨q.val, by omega⟩ : Fin 10) ≠ anc := by
  intro h
  have hv := congrArg Fin.val h
  simp [anc, qq] at hv
  omega

theorem dataPhys_eq_physOfData (q : DataQ) :
    (⟨q.val, by omega⟩ : Fin 10) = physOfData q := by
  apply Fin.ext
  rfl

def zNoZ (es : ErrorState 10) : Prop := zPart (es.paulis anc) = Pauli.I
def xNoX (es : ErrorState 10) : Prop := xPart (es.paulis anc) = Pauli.I

theorem zPart_anc_mul_eq_self (es : ErrorState 10) (i : Fin 10) (hZ : zNoZ es) :
    pauliMul (zPart (es.paulis anc)) (es.paulis i) = es.paulis i := by
  unfold zNoZ at hZ
  cases hAnc : es.paulis anc <;> simp [hAnc, zPart] at hZ ⊢

theorem xPart_anc_mul_eq_self (es : ErrorState 10) (i : Fin 10) (hX : xNoX es) :
    pauliMul (xPart (es.paulis anc)) (es.paulis i) = es.paulis i := by
  unfold xNoX at hX
  cases hAnc : es.paulis anc <;> simp [hAnc, xPart] at hX ⊢

theorem zPart_q9_mul_eq_self (es : ErrorState 10) (i : Fin 10) (hZ : zNoZ es) :
    pauliMul (zPart (es.paulis (qq 9))) (es.paulis i) = es.paulis i := by
  simpa [anc] using zPart_anc_mul_eq_self es i hZ

theorem xPart_q9_mul_eq_self (es : ErrorState 10) (i : Fin 10) (hX : xNoX es) :
    pauliMul (xPart (es.paulis (qq 9))) (es.paulis i) = es.paulis i := by
  simpa [anc] using xPart_anc_mul_eq_self es i hX

theorem dataPart_prepZero_anc (es : ErrorState 10) :
    dataPart (propagateGate (.prepZero anc) es) = dataPart es := by
  funext d
  have hne := dataPhys_ne_anc d
  simp [dataPart, propagateGate, hne]

theorem dataPart_prepPlus_anc (es : ErrorState 10) :
    dataPart (propagateGate (.prepPlus anc) es) = dataPart es := by
  funext d
  have hne := dataPhys_ne_anc d
  simp [dataPart, propagateGate, hne]

theorem dataPart_h_anc (es : ErrorState 10) :
    dataPart (propagateGate (.hadamard anc) es) = dataPart es := by
  funext d
  have hne := dataPhys_ne_anc d
  simp [dataPart, propagateGate, hne]

theorem dataPart_measZ_anc (es : ErrorState 10) :
    dataPart (propagateGate (.measZ anc) es) = dataPart es := by
  funext d
  simp [dataPart, propagateGate]

theorem zNoZ_prepZero_anc (es : ErrorState 10) : zNoZ (propagateGate (.prepZero anc) es) := by
  simp [zNoZ, anc, propagateGate, zPart]

theorem xNoX_prepPlus_anc (es : ErrorState 10) : xNoX (propagateGate (.prepPlus anc) es) := by
  simp [xNoX, anc, propagateGate, xPart]

theorem dataPart_cnot_data_to_anc (q : DataQ) (es : ErrorState 10) (hZ : zNoZ es) :
    dataPart (propagateGate (.cnot (physOfData q) anc (physOfData_ne_anc' q)) es) =
      dataPart es := by
  fin_cases q <;> funext d <;> fin_cases d <;>
    simp [dataPart, propagateGate, physOfData, anc, qq]
  all_goals simpa [qq] using zPart_q9_mul_eq_self es _ hZ

theorem zNoZ_cnot_data_to_anc (q : DataQ) (es : ErrorState 10) (hZ : zNoZ es) :
    zNoZ (propagateGate (.cnot (physOfData q) anc (physOfData_ne_anc' q)) es) := by
  unfold zNoZ at hZ ⊢
  simp [anc] at hZ ⊢
  cases hAnc : es.paulis (qq 9) <;> simp [hAnc, zPart] at hZ
  · cases hq : es.paulis (physOfData q) <;>
      simp [propagateGate, hAnc, hq, xPart, zPart, pauliMul]
  · cases hq : es.paulis (physOfData q) <;>
      simp [propagateGate, hAnc, hq, xPart, zPart, pauliMul]

theorem dataPart_cnot_anc_to_data (q : DataQ) (es : ErrorState 10) (hX : xNoX es) :
    dataPart (propagateGate (.cnot anc (physOfData q) (Ne.symm (physOfData_ne_anc' q))) es) =
      dataPart es := by
  fin_cases q <;> funext d <;> fin_cases d <;>
    simp [dataPart, propagateGate, physOfData, anc, qq]
  all_goals simpa [qq] using xPart_q9_mul_eq_self es _ hX

theorem xNoX_cnot_anc_to_data (q : DataQ) (es : ErrorState 10) (hX : xNoX es) :
    xNoX (propagateGate (.cnot anc (physOfData q) (Ne.symm (physOfData_ne_anc' q))) es) := by
  unfold xNoX at hX ⊢
  simp [anc] at hX ⊢
  have hne : qq 9 ≠ physOfData q := by
    simpa [anc] using Ne.symm (physOfData_ne_anc' q)
  cases hAnc : es.paulis (qq 9) <;> simp [hAnc, xPart] at hX
  · cases hq : es.paulis (physOfData q) <;>
      simp [propagateGate, hne, hAnc, hq, xPart, zPart, pauliMul]
  · cases hq : es.paulis (physOfData q) <;>
      simp [propagateGate, hne, hAnc, hq, xPart, zPart, pauliMul]

def zCNOTs (order : List DataQ) : Circuit 10 :=
  order.map fun q => .cnot (physOfData q) anc (physOfData_ne_anc' q)

def xCNOTs (order : List DataQ) : Circuit 10 :=
  order.map fun q => .cnot anc (physOfData q) (Ne.symm (physOfData_ne_anc' q))

theorem dataPart_zCNOTs :
    ∀ (order : List DataQ) (es : ErrorState 10),
      zNoZ es ->
      dataPart (propagateCircuit (zCNOTs order) es) = dataPart es ∧
        zNoZ (propagateCircuit (zCNOTs order) es)
  | [], es, hZ => by
      simp [zCNOTs, propagateCircuit, hZ]
  | q :: qs, es, hZ => by
      have hStepData := dataPart_cnot_data_to_anc q es hZ
      have hStepZ := zNoZ_cnot_data_to_anc q es hZ
      rcases dataPart_zCNOTs qs
          (propagateGate (.cnot (physOfData q) anc (physOfData_ne_anc' q)) es) hStepZ with
        ⟨hTailData, hTailZ⟩
      constructor
      · simp [zCNOTs, propagateCircuit]
        exact hTailData.trans hStepData
      · simpa [zCNOTs, propagateCircuit] using hTailZ

theorem dataPart_xCNOTs :
    ∀ (order : List DataQ) (es : ErrorState 10),
      xNoX es ->
      dataPart (propagateCircuit (xCNOTs order) es) = dataPart es ∧
        xNoX (propagateCircuit (xCNOTs order) es)
  | [], es, hX => by
      simp [xCNOTs, propagateCircuit, hX]
  | q :: qs, es, hX => by
      have hStepData := dataPart_cnot_anc_to_data q es hX
      have hStepX := xNoX_cnot_anc_to_data q es hX
      rcases dataPart_xCNOTs qs
          (propagateGate (.cnot anc (physOfData q) (Ne.symm (physOfData_ne_anc' q))) es) hStepX with
        ⟨hTailData, hTailX⟩
      constructor
      · simp [xCNOTs, propagateCircuit]
        exact hTailData.trans hStepData
      · simpa [xCNOTs, propagateCircuit] using hTailX

theorem propagateCircuit_append (a b : Circuit 10) (es : ErrorState 10) :
    propagateCircuit (a ++ b) es = propagateCircuit b (propagateCircuit a es) := by
  induction a generalizing es with
  | nil => rfl
  | cons g gs ih =>
      simp [propagateCircuit, ih]

theorem eraseFaults_zGadget_tail (order : List DataQ) :
    eraseFaults
      ((order.map (fun q =>
        let qp := physOfData q
        [FInstr.errLoc qp, FInstr.errLoc (qq 9),
          FInstr.gate (.cnot qp (qq 9) (physOfData_ne_anc q))])).flatten ++
        [FInstr.errLoc (qq 9), FInstr.gate (.measZ (qq 9))]) =
      zCNOTs order ++ [.measZ anc] := by
  induction order with
  | nil =>
      simp [zCNOTs, eraseFaults, anc]
  | cons q qs ih =>
      simp [zCNOTs, eraseFaults, ih, anc]

theorem eraseFaults_xGadget_tail (order : List DataQ) :
    eraseFaults
      ((order.map (fun q =>
        let qp := physOfData q
        [FInstr.errLoc (qq 9), FInstr.errLoc qp,
          FInstr.gate (.cnot (qq 9) qp (Ne.symm (physOfData_ne_anc q)))])).flatten ++
        [FInstr.errLoc (qq 9), FInstr.gate (.hadamard (qq 9)),
          FInstr.errLoc (qq 9), FInstr.gate (.measZ (qq 9))]) =
      xCNOTs order ++ [.hadamard anc, .measZ anc] := by
  induction order with
  | nil =>
      simp [xCNOTs, eraseFaults, anc]
  | cons q qs ih =>
      simp [xCNOTs, eraseFaults, ih, anc]

theorem eraseFaults_zGadget (order : List DataQ) :
    eraseFaults (zGadget order) = .prepZero anc :: zCNOTs order ++ [.measZ anc] := by
  unfold zGadget
  simp [eraseFaults]
  simpa [anc] using eraseFaults_zGadget_tail order

theorem eraseFaults_xGadget (order : List DataQ) :
    eraseFaults (xGadget order) =
      .prepPlus anc :: xCNOTs order ++ [.hadamard anc, .measZ anc] := by
  unfold xGadget
  simp [eraseFaults]
  simpa [anc] using eraseFaults_xGadget_tail order

theorem dataPart_det_zGadget (order : List DataQ) (es : ErrorState 10) :
    dataPart (propagateCircuit (eraseFaults (zGadget order)) es) = dataPart es := by
  rw [eraseFaults_zGadget]
  change dataPart (propagateCircuit (zCNOTs order ++ [.measZ anc])
    (propagateGate (.prepZero anc) es)) = dataPart es
  rw [propagateCircuit_append]
  rcases dataPart_zCNOTs order (propagateGate (.prepZero anc) es)
      (zNoZ_prepZero_anc es) with ⟨hData, _⟩
  calc
    dataPart (propagateCircuit [.measZ anc]
        (propagateCircuit (zCNOTs order) (propagateGate (.prepZero anc) es))) =
        dataPart (propagateCircuit (zCNOTs order) (propagateGate (.prepZero anc) es)) := by
          simp [propagateCircuit, dataPart_measZ_anc]
    _ = dataPart (propagateGate (.prepZero anc) es) := hData
    _ = dataPart es := dataPart_prepZero_anc es

theorem dataPart_det_xGadget (order : List DataQ) (es : ErrorState 10) :
    dataPart (propagateCircuit (eraseFaults (xGadget order)) es) = dataPart es := by
  rw [eraseFaults_xGadget]
  change dataPart (propagateCircuit (xCNOTs order ++ [.hadamard anc, .measZ anc])
    (propagateGate (.prepPlus anc) es)) = dataPart es
  rw [propagateCircuit_append]
  rcases dataPart_xCNOTs order (propagateGate (.prepPlus anc) es)
      (xNoX_prepPlus_anc es) with ⟨hData, _⟩
  calc
    dataPart (propagateCircuit [.hadamard anc, .measZ anc]
        (propagateCircuit (xCNOTs order) (propagateGate (.prepPlus anc) es))) =
        dataPart (propagateCircuit (xCNOTs order) (propagateGate (.prepPlus anc) es)) := by
          simp [propagateCircuit, dataPart_h_anc, dataPart_measZ_anc]
    _ = dataPart (propagateGate (.prepPlus anc) es) := hData
    _ = dataPart es := dataPart_prepPlus_anc es

def logicalFailure (es : ErrorState 10) : Prop :=
  QStab.Paper.SurfaceD3CircuitDistance.LogicalAny (dataPart es)

def cleanPre : AssertionF 10 := fun σ => σ = QCState.clean 10

def distPost : AssertionF 10 :=
  fun σ => σ.lambda ≤ 2 -> ¬ logicalFailure σ.es

def frontier (suffix : Circuit 10) : AssertionF 10 :=
  fun σ =>
    QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR
      (dataPart (propagateCircuit suffix σ.es)) σ.lambda

def esMul (A B : ErrorState 10) : ErrorState 10 where
  paulis := fun q => pauliMul (A.paulis q) (B.paulis q)
  measFlips := fun _ => false

theorem pauliMul_eq (a b : Pauli) : pauliMul a b = Pauli.mul a b := by
  cases a <;> cases b <;> rfl

theorem pauliMul_comm (a b : Pauli) : pauliMul a b = pauliMul b a := by
  cases a <;> cases b <;> rfl

theorem pauliMul_assoc (a b c : Pauli) :
    pauliMul (pauliMul a b) c = pauliMul a (pauliMul b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem dataPart_esMul (A B : ErrorState 10) :
    dataPart (esMul A B) =
      QStab.Paper.SurfaceD3CircuitDistance.pmul (dataPart A) (dataPart B) := by
  funext q
  simp [dataPart, esMul, QStab.Paper.SurfaceD3CircuitDistance.pmul, pauliMul_eq]

theorem propagateGate_paulis_congr (g : Gate 10) {A B : ErrorState 10}
    (h : A.paulis = B.paulis) :
    (propagateGate g A).paulis = (propagateGate g B).paulis := by
  funext i
  cases g <;> simp [propagateGate, h]

theorem propagateCircuit_paulis_congr :
    ∀ (suffix : Circuit 10) {A B : ErrorState 10},
      A.paulis = B.paulis ->
      (propagateCircuit suffix A).paulis = (propagateCircuit suffix B).paulis
  | [], A, B, h => h
  | g :: gs, A, B, h => by
      exact propagateCircuit_paulis_congr gs (propagateGate_paulis_congr g h)

theorem propagateGate_paulis_esMul (g : Gate 10) (A B : ErrorState 10) :
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
        cases A.paulis c <;> cases B.paulis c <;>
          cases A.paulis t <;> cases B.paulis t <;> rfl
      · by_cases hc : i = c
        · have hct : c ≠ t := by
            intro h
            exact ht (by simpa [h] using hc)
          simp [propagateGate, esMul, hc, hct]
          cases A.paulis t <;> cases B.paulis t <;>
            cases A.paulis c <;> cases B.paulis c <;> rfl
        · simp [propagateGate, esMul, ht, hc]

theorem propagateCircuit_paulis_esMul :
    ∀ (suffix : Circuit 10) (A B : ErrorState 10),
      (propagateCircuit suffix (esMul A B)).paulis =
        (esMul (propagateCircuit suffix A) (propagateCircuit suffix B)).paulis
  | [], A, B => rfl
  | g :: gs, A, B => by
      have hstart := propagateGate_paulis_esMul g A B
      have hcongr := propagateCircuit_paulis_congr gs hstart
      exact hcongr.trans (propagateCircuit_paulis_esMul gs (propagateGate g A) (propagateGate g B))

def singleError (q : Fin 10) (p : Pauli) : ErrorState 10 :=
  (ErrorState.clean 10).inject q p

theorem inject_paulis_eq_esMul_single (es : ErrorState 10) (q : Fin 10) (p : Pauli) :
    (es.inject q p).paulis = (esMul (singleError q p) es).paulis := by
  funext i
  by_cases h : i = q
  · subst h
    simp [ErrorState.inject, singleError, esMul, ErrorState.clean, pauliMul_eq]
    cases p <;> cases es.paulis i <;> rfl
  · simp [ErrorState.inject, singleError, esMul, ErrorState.clean, h, pauliMul_eq]
    cases es.paulis i <;> rfl

def qFaultDelta (q : Fin 10) (suffix : Circuit 10) (p : Pauli) : DataPauli :=
  dataPart (propagateCircuit suffix (singleError q p))

def QSiteSafe (q : Fin 10) (suffix : Circuit 10) : Prop :=
  ∀ p, p ≠ Pauli.I ->
    QStab.Paper.SurfaceD3CircuitDistance.DeltaSafeFast (qFaultDelta q suffix p)

theorem dataPart_propagate_inject (suffix : Circuit 10)
    (es : ErrorState 10) (q : Fin 10) (p : Pauli) :
    dataPart (propagateCircuit suffix (es.inject q p)) =
      QStab.Paper.SurfaceD3CircuitDistance.pmul
        (dataPart (propagateCircuit suffix es))
        (qFaultDelta q suffix p) := by
  have hInject := inject_paulis_eq_esMul_single es q p
  have hCong := propagateCircuit_paulis_congr suffix hInject
  have hMul := propagateCircuit_paulis_esMul suffix (singleError q p) es
  funext d
  have hpoint := congrFun (hCong.trans hMul) ⟨d.val, by omega⟩
  change (propagateCircuit suffix (es.inject q p)).paulis ⟨d.val, by omega⟩ =
    Pauli.mul ((propagateCircuit suffix es).paulis ⟨d.val, by omega⟩)
      ((propagateCircuit suffix (singleError q p)).paulis ⟨d.val, by omega⟩)
  rw [hpoint]
  simp [esMul, pauliMul_eq]
  cases (propagateCircuit suffix (singleError q p)).paulis ⟨d.val, by omega⟩ <;>
    cases (propagateCircuit suffix es).paulis ⟨d.val, by omega⟩ <;> rfl

instance instDecidableQSiteSafe (q : Fin 10) (suffix : Circuit 10) :
    Decidable (QSiteSafe q suffix) := by
  unfold QSiteSafe
  infer_instance

theorem frontier_errLoc_pre {q : Fin 10} {suffix : Circuit 10}
    (hSafe : QSiteSafe q suffix) :
    ∀ σ, frontier suffix σ ->
      frontier suffix σ ∧
        ∀ p, p ≠ Pauli.I -> frontier suffix ⟨σ.es.inject q p, σ.lambda + 1⟩ := by
  intro σ hFront
  refine ⟨hFront, ?_⟩
  intro p hp
  unfold frontier
  rw [dataPart_propagate_inject suffix σ.es q p]
  exact QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR_pmul_of_delta_safe hFront
    (QStab.Paper.SurfaceD3CircuitDistance.DeltaSafe_of_fast (hSafe p hp))

def errLocDeriv (q : Fin 10) (suffix : Circuit 10) (hSafe : QSiteSafe q suffix) :
    FDeriv (frontier suffix) [.errLoc q] (frontier suffix) :=
  FDeriv.F_Conseq (FDeriv.F_ErrLoc q (frontier suffix))
    (frontier_errLoc_pre hSafe) (fun _ h => h)

def AllSitesSafe : FCircuit 10 -> Prop
  | [] => True
  | .gate _ :: rest => AllSitesSafe rest
  | .errLoc q :: rest => QSiteSafe q (eraseFaults rest) ∧ AllSitesSafe rest

instance instDecidableAllSitesSafe : (fc : FCircuit 10) -> Decidable (AllSitesSafe fc)
  | [] => isTrue trivial
  | .gate _ :: rest => instDecidableAllSitesSafe rest
  | .errLoc q :: rest =>
      match instDecidableQSiteSafe q (eraseFaults rest), instDecidableAllSitesSafe rest with
      | isTrue hq, isTrue hr => isTrue ⟨hq, hr⟩
      | isFalse hnq, _ => isFalse (fun h => hnq h.1)
      | _, isFalse hnr => isFalse (fun h => hnr h.2)

def frontierDeriv :
    ∀ (fc : FCircuit 10), AllSitesSafe fc ->
      FDeriv (frontier (eraseFaults fc)) fc (frontier [])
  | [], _ => FDeriv.F_Nil (frontier [])
  | .gate g :: rest, hSafe =>
      FDeriv.F_App (FDeriv.F_Gate g (frontier (eraseFaults rest)))
        (frontierDeriv rest hSafe)
  | .errLoc q :: rest, hSafe =>
      FDeriv.F_App (errLocDeriv q (eraseFaults rest) hSafe.1)
        (frontierDeriv rest hSafe.2)

theorem allSitesSafe_G0 : AllSitesSafe G0 := by
  simp [G0, zGadget, G0Order, dq, qq, physOfData, eraseFaults, AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem allSitesSafe_G1 : AllSitesSafe G1 := by
  simp [G1, xGadget, G1Order, dq, qq, physOfData, eraseFaults, AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem allSitesSafe_G2 : AllSitesSafe G2 := by
  simp [G2, xGadget, G2Order, dq, qq, physOfData, eraseFaults, AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem allSitesSafe_G3 : AllSitesSafe G3 := by
  simp [G3, zGadget, G3Order, dq, qq, physOfData, eraseFaults, AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem allSitesSafe_G4 : AllSitesSafe G4 := by
  simp [G4, xGadget, G4Order, dq, qq, physOfData, eraseFaults, AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem allSitesSafe_G5 : AllSitesSafe G5 := by
  simp [G5, zGadget, G5Order, dq, qq, physOfData, eraseFaults, AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem allSitesSafe_G6 : AllSitesSafe G6 := by
  simp [G6, zGadget, G6Order, dq, qq, physOfData, eraseFaults, AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

theorem allSitesSafe_G7 : AllSitesSafe G7 := by
  simp [G7, xGadget, G7Order, dq, qq, physOfData, eraseFaults, AllSitesSafe, QSiteSafe]
  repeat first
    | constructor
    | intro p hp
      cases p <;> simp at hp ⊢ <;> decide

def gadgetDeriv (gadget : FCircuit 10)
    (hSafe : AllSitesSafe gadget)
    (hData : ∀ es, dataPart (propagateCircuit (eraseFaults gadget) es) = dataPart es) :
    FDeriv (frontier []) gadget (frontier []) :=
  FDeriv.F_Conseq (frontierDeriv gadget hSafe)
    (fun σ hFront => by
      unfold frontier at hFront ⊢
      rw [hData σ.es]
      exact hFront)
    (fun _ h => h)

def G0Deriv : FDeriv (frontier []) G0 (frontier []) :=
  gadgetDeriv G0 allSitesSafe_G0 (by intro es; simpa [G0] using dataPart_det_zGadget G0Order es)

def G1Deriv : FDeriv (frontier []) G1 (frontier []) :=
  gadgetDeriv G1 allSitesSafe_G1 (by intro es; simpa [G1] using dataPart_det_xGadget G1Order es)

def G2Deriv : FDeriv (frontier []) G2 (frontier []) :=
  gadgetDeriv G2 allSitesSafe_G2 (by intro es; simpa [G2] using dataPart_det_xGadget G2Order es)

def G3Deriv : FDeriv (frontier []) G3 (frontier []) :=
  gadgetDeriv G3 allSitesSafe_G3 (by intro es; simpa [G3] using dataPart_det_zGadget G3Order es)

def G4Deriv : FDeriv (frontier []) G4 (frontier []) :=
  gadgetDeriv G4 allSitesSafe_G4 (by intro es; simpa [G4] using dataPart_det_xGadget G4Order es)

def G5Deriv : FDeriv (frontier []) G5 (frontier []) :=
  gadgetDeriv G5 allSitesSafe_G5 (by intro es; simpa [G5] using dataPart_det_zGadget G5Order es)

def G6Deriv : FDeriv (frontier []) G6 (frontier []) :=
  gadgetDeriv G6 allSitesSafe_G6 (by intro es; simpa [G6] using dataPart_det_zGadget G6Order es)

def G7Deriv : FDeriv (frontier []) G7 (frontier []) :=
  gadgetDeriv G7 allSitesSafe_G7 (by intro es; simpa [G7] using dataPart_det_xGadget G7Order es)

def surfaceD3FrontierDeriv : FDeriv (frontier []) C_NZ_D3 (frontier []) :=
  FDeriv.F_App G0Deriv <|
    FDeriv.F_App G1Deriv <|
      FDeriv.F_App G2Deriv <|
        FDeriv.F_App G3Deriv <|
          FDeriv.F_App G4Deriv <|
            FDeriv.F_App G5Deriv <|
              FDeriv.F_App G6Deriv G7Deriv

theorem clean_to_frontier :
    ∀ σ, cleanPre σ -> frontier [] σ := by
  intro σ hσ
  subst hσ
  unfold frontier
  have hData :
      dataPart (propagateCircuit [] (QCState.clean 10).es) =
        QStab.Paper.SurfaceD3CircuitDistance.dataI := by
    funext q
    simp [dataPart, QStab.Paper.SurfaceD3CircuitDistance.dataI, propagateCircuit,
      ErrorState.clean]
  rw [hData]
  exact QStab.Paper.SurfaceD3CircuitDistance.OBL_INIT

theorem frontier_to_distPost :
    ∀ σ, frontier [] σ -> distPost σ := by
  intro σ hFront hBudget hFail
  unfold frontier at hFront
  simp [propagateCircuit] at hFront
  have hDist := QStab.Paper.SurfaceD3CircuitDistance.data_distance_from_BI_PAIR hFront hFail
  omega

def surfaceD3Deriv : FDeriv cleanPre C_NZ_D3 distPost :=
  FDeriv.F_Conseq surfaceD3FrontierDeriv clean_to_frontier frontier_to_distPost

theorem surfaceD3_hoare :
    FHoare cleanPre C_NZ_D3 distPost :=
  fhoare_sound surfaceD3Deriv

theorem surfaceD3_tolerates_two_faults :
    ToleratesFaultsΛ C_NZ_D3 logicalFailure 2 :=
  toleratesFaultsΛ_of_hoare C_NZ_D3 logicalFailure 2 surfaceD3_hoare

def runFScript : FCircuit 10 -> List (Option Pauli) -> ErrorState 10 -> ErrorState 10 × Nat
  | [], _, es => (es, 0)
  | .gate g :: rest, script, es => runFScript rest script (propagateGate g es)
  | .errLoc _ :: rest, [], es => runFScript rest [] es
  | .errLoc _ :: rest, none :: script, es => runFScript rest script es
  | .errLoc q :: rest, some p :: script, es =>
      if p = Pauli.I then
        runFScript rest script es
      else
        let out := runFScript rest script (es.inject q p)
        (out.1, out.2 + 1)

theorem runFScript_sound :
    ∀ (fc : FCircuit 10) (script : List (Option Pauli)) (es : ErrorState 10),
      fcevalW (runFScript fc script es).2 fc es (runFScript fc script es).1 := by
  intro fc
  induction fc with
  | nil =>
      intro script es
      simp [runFScript, fcevalW.nil]
  | cons i rest ih =>
      intro script es
      cases i with
      | gate g =>
          exact fcevalW.gate g rest es (runFScript rest script (propagateGate g es)).1
            (runFScript rest script (propagateGate g es)).2 (ih script (propagateGate g es))
      | errLoc q =>
          cases script with
          | nil =>
              exact fcevalW.idle q rest es (runFScript rest [] es).1
                (runFScript rest [] es).2 (ih [] es)
          | cons step script =>
              cases step with
              | none =>
                  exact fcevalW.idle q rest es (runFScript rest script es).1
                    (runFScript rest script es).2 (ih script es)
              | some p =>
                  by_cases hpI : p = Pauli.I
                  · simp [runFScript, hpI]
                    exact fcevalW.idle q rest es (runFScript rest script es).1
                      (runFScript rest script es).2 (ih script es)
                  · simp [runFScript, hpI]
                    exact fcevalW.inject q rest es
                      (runFScript rest script (es.inject q p)).1 p hpI
                      (runFScript rest script (es.inject q p)).2
                      (ih script (es.inject q p))

def reachLogicalXScript : List (Option Pauli) :=
  (List.range (QStab.Paper.SurfaceD3CircuitDistance.C_NZ_D3_sites.length)).map fun i =>
    if i = 1 ∨ i = 3 ∨ i = 27 then some Pauli.X else none

theorem reachLogicalXScript_faults :
    (runFScript C_NZ_D3 reachLogicalXScript (ErrorState.clean 10)).2 = 3 := by
  unfold C_NZ_D3 G0 G1 G2 G3 G4 G5 G6 G7 zGadget xGadget
  unfold G0Order G1Order G2Order G3Order G4Order G5Order G6Order G7Order
  unfold reachLogicalXScript runFScript
  decide

theorem reachLogicalXScript_data :
    dataPart (runFScript C_NZ_D3 reachLogicalXScript (ErrorState.clean 10)).1 =
      QStab.Paper.SurfaceD3CircuitDistance.logicalX := by
  funext q
  fin_cases q <;>
    unfold C_NZ_D3 G0 G1 G2 G3 G4 G5 G6 G7 zGadget xGadget <;>
    unfold G0Order G1Order G2Order G3Order G4Order G5Order G6Order G7Order <;>
    unfold reachLogicalXScript runFScript dataPart physOfData qq dq <;>
    decide

theorem surfaceD3_reachable_three_fault_logical :
    ∃ es, fcevalW 3 C_NZ_D3 (ErrorState.clean 10) es ∧ logicalFailure es := by
  let out := runFScript C_NZ_D3 reachLogicalXScript (ErrorState.clean 10)
  refine ⟨out.1, ?_, ?_⟩
  · have h := runFScript_sound C_NZ_D3 reachLogicalXScript (ErrorState.clean 10)
    simpa [out, reachLogicalXScript_faults] using h
  · unfold logicalFailure
    have hData := reachLogicalXScript_data
    simpa [out, hData] using QStab.Paper.SurfaceD3CircuitDistance.logicalX_real

theorem surfaceD3_distance_exact_qclifford :
    ToleratesFaultsΛ C_NZ_D3 logicalFailure 2 ∧
      ∃ es, fcevalW 3 C_NZ_D3 (ErrorState.clean 10) es ∧ logicalFailure es :=
  ⟨surfaceD3_tolerates_two_faults, surfaceD3_reachable_three_fault_logical⟩

/-! ## Lean/certificate correspondence emitter -/

def jsonQuote (s : String) : String :=
  "\"" ++ s ++ "\""

def jsonArray (xs : List String) : String :=
  "[" ++ String.intercalate "," xs ++ "]"

def jsonObject (xs : List (String × String)) : String :=
  "{" ++ String.intercalate "," (xs.map fun (k, v) => jsonQuote k ++ ":" ++ v) ++ "}"

def pauliJsonName? : Pauli -> Option String
  | .I => none
  | .X => some "X"
  | .Y => some "Y"
  | .Z => some "Z"

def pauliSupportJson (E : DataPauli) : String :=
  jsonArray <| (List.finRange 9).filterMap fun q =>
    (pauliJsonName? (E q)).map fun p => jsonArray [toString q.val, jsonQuote p]

def stabJson (name : String) (E : DataPauli) : String :=
  jsonObject [("name", jsonQuote name), ("support", pauliSupportJson E)]

def logicalsJson : String :=
  jsonObject [
    ("LX", pauliSupportJson QStab.Paper.SurfaceD3CircuitDistance.logicalX),
    ("LZ", pauliSupportJson QStab.Paper.SurfaceD3CircuitDistance.logicalZ)
  ]

def orderJson (order : List DataQ) : String :=
  jsonArray (order.map fun q => toString q.val)

def gadgetJson (id kind : String) (order : List DataQ) : String :=
  jsonObject [("id", jsonQuote id), ("kind", jsonQuote kind), ("order", orderJson order)]

def qcliffordCertificateJson : String :=
  jsonObject [
    ("stabilizers", jsonArray [
      stabJson "s0" QStab.Paper.SurfaceD3CircuitDistance.s0,
      stabJson "s1" QStab.Paper.SurfaceD3CircuitDistance.s1,
      stabJson "s2" QStab.Paper.SurfaceD3CircuitDistance.s2,
      stabJson "s3" QStab.Paper.SurfaceD3CircuitDistance.s3,
      stabJson "s4" QStab.Paper.SurfaceD3CircuitDistance.s4,
      stabJson "s5" QStab.Paper.SurfaceD3CircuitDistance.s5,
      stabJson "s6" QStab.Paper.SurfaceD3CircuitDistance.s6,
      stabJson "s7" QStab.Paper.SurfaceD3CircuitDistance.s7
    ]),
    ("logicals", logicalsJson),
    ("gadgets", jsonArray [
      gadgetJson "G0" "MeasZStab" G0Order,
      gadgetJson "G1" "MeasXStab" G1Order,
      gadgetJson "G2" "MeasXStab" G2Order,
      gadgetJson "G3" "MeasZStab" G3Order,
      gadgetJson "G4" "MeasXStab" G4Order,
      gadgetJson "G5" "MeasZStab" G5Order,
      gadgetJson "G6" "MeasZStab" G6Order,
      gadgetJson "G7" "MeasXStab" G7Order
    ]),
    ("distance", toString distanceBound)
  ]

#eval IO.println ("QCLIFFORD_CERT_CORRESPONDENCE_JSON:" ++ qcliffordCertificateJson)

#check surfaceD3Deriv
#print axioms surfaceD3_tolerates_two_faults
#print axioms surfaceD3_reachable_three_fault_logical
#print axioms surfaceD3_distance_exact_qclifford

end QStab.QClifford.SurfaceD3Distance
