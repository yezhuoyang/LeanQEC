import LeanQEC.Pauli
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option maxRecDepth 8192

/-!
# Surface-d3 NZ QClifford circuit-distance kernel proof

This file mirrors the concrete certificate checked by
`tools/check_geometric_hoare.py` for the distance-3 rotated surface code with
the eight-gadget NZ schedule.

Choice about detection bits: the main theorem below proves the stronger
detection-free lower bound.  The `ZeroDet` hypothesis from `DIST_CIRC_D3` is
therefore added only in the wrapper theorem `surfaceD3_DIST_CIRC_D3`.
-/

namespace QStab.Paper.SurfaceD3CircuitDistance

deriving instance Fintype for Pauli

abbrev DataQ := Fin 9
abbrev PhysQ := Fin 10
abbrev StabIdx := Fin 8
abbrev RowCol := Fin 3

abbrev DataPauli := DataQ -> Pauli
abbrev PhysPauli := PhysQ -> Pauli
abbrev StabMask := StabIdx -> Bool
abbrev DetVec := StabIdx -> Bool

instance instFintypeDataPauli : Fintype DataPauli := inferInstance
instance instDecidableEqDataPauli : DecidableEq DataPauli := inferInstance
instance instFintypePhysPauli : Fintype PhysPauli := inferInstance
instance instDecidableEqPhysPauli : DecidableEq PhysPauli := inferInstance
instance instFintypeStabMask : Fintype StabMask := inferInstance
instance instDecidableEqStabMask : DecidableEq StabMask := inferInstance
instance instFintypeDetVec : Fintype DetVec := inferInstance
instance instDecidableEqDetVec : DecidableEq DetVec := inferInstance

def dataI : DataPauli := fun _ => .I
def physI : PhysPauli := fun _ => .I

def pmul (E F : DataPauli) : DataPauli := fun q => Pauli.mul (E q) (F q)
def phMul (E F : PhysPauli) : PhysPauli := fun q => Pauli.mul (E q) (F q)

def hasX : Pauli -> Bool
  | .X | .Y => true
  | _ => false

def hasZ : Pauli -> Bool
  | .Z | .Y => true
  | _ => false

def xPart : Pauli -> Pauli
  | .X | .Y => .X
  | _ => .I

def zPart : Pauli -> Pauli
  | .Z | .Y => .Z
  | _ => .I

def hadamardAction : Pauli -> Pauli
  | .X => .Z
  | .Z => .X
  | .Y => .Y
  | .I => .I

def anticommutes : Pauli -> Pauli -> Bool
  | .I, _ => false
  | _, .I => false
  | .X, .X => false
  | .Y, .Y => false
  | .Z, .Z => false
  | _, _ => true

def dq (n : Nat) (h : n < 9 := by decide) : DataQ := ⟨n, h⟩
def pq (n : Nat) (h : n < 10 := by decide) : PhysQ := ⟨n, h⟩

theorem dataq0_eq_dq (h : 0 < 9) : (⟨0, h⟩ : DataQ) = dq 0 := by
  apply Fin.ext
  rfl

theorem dataq1_eq_dq (h : 1 < 9) : (⟨1, h⟩ : DataQ) = dq 1 := by
  apply Fin.ext
  rfl

theorem dataq2_eq_dq (h : 2 < 9) : (⟨2, h⟩ : DataQ) = dq 2 := by
  apply Fin.ext
  rfl

theorem dataq3_eq_dq (h : 3 < 9) : (⟨3, h⟩ : DataQ) = dq 3 := by
  apply Fin.ext
  rfl

theorem dataq4_eq_dq (h : 4 < 9) : (⟨4, h⟩ : DataQ) = dq 4 := by
  apply Fin.ext
  rfl

theorem dataq5_eq_dq (h : 5 < 9) : (⟨5, h⟩ : DataQ) = dq 5 := by
  apply Fin.ext
  rfl

theorem dataq6_eq_dq (h : 6 < 9) : (⟨6, h⟩ : DataQ) = dq 6 := by
  apply Fin.ext
  rfl

theorem dataq7_eq_dq (h : 7 < 9) : (⟨7, h⟩ : DataQ) = dq 7 := by
  apply Fin.ext
  rfl

theorem dataq8_eq_dq (h : 8 < 9) : (⟨8, h⟩ : DataQ) = dq 8 := by
  apply Fin.ext
  rfl

def singleData (q : DataQ) (p : Pauli) : DataPauli :=
  fun i => if i = q then p else .I

def singlePhys (q : PhysQ) (p : Pauli) : PhysPauli :=
  fun i => if i = q then p else .I

def ofDataList (xs : List (Nat × Pauli)) : DataPauli :=
  fun q => (xs.lookup q.val).getD .I

def s0 (q : DataQ) : Pauli :=
  match q.val with
  | 0 | 1 | 3 | 4 => .Z
  | _ => .I

def s1 (q : DataQ) : Pauli :=
  match q.val with
  | 1 | 2 | 4 | 5 => .X
  | _ => .I

def s2 (q : DataQ) : Pauli :=
  match q.val with
  | 3 | 4 | 6 | 7 => .X
  | _ => .I

def s3 (q : DataQ) : Pauli :=
  match q.val with
  | 4 | 5 | 7 | 8 => .Z
  | _ => .I

def s4 (q : DataQ) : Pauli :=
  match q.val with
  | 0 | 1 => .X
  | _ => .I

def s5 (q : DataQ) : Pauli :=
  match q.val with
  | 2 | 5 => .Z
  | _ => .I

def s6 (q : DataQ) : Pauli :=
  match q.val with
  | 3 | 6 => .Z
  | _ => .I

def s7 (q : DataQ) : Pauli :=
  match q.val with
  | 7 | 8 => .X
  | _ => .I

def stabAt (i : StabIdx) : DataPauli :=
  match i.val with
  | 0 => s0
  | 1 => s1
  | 2 => s2
  | 3 => s3
  | 4 => s4
  | 5 => s5
  | 6 => s6
  | _ => s7

def logicalX (q : DataQ) : Pauli :=
  match q.val with
  | 0 | 3 | 6 => .X
  | _ => .I

def logicalZ (q : DataQ) : Pauli :=
  match q.val with
  | 0 | 1 | 2 => .Z
  | _ => .I

def parity (S E : DataPauli) : Bool :=
  xor (anticommutes (S 0) (E 0))
  (xor (anticommutes (S 1) (E 1))
  (xor (anticommutes (S 2) (E 2))
  (xor (anticommutes (S 3) (E 3))
  (xor (anticommutes (S 4) (E 4))
  (xor (anticommutes (S 5) (E 5))
  (xor (anticommutes (S 6) (E 6))
  (xor (anticommutes (S 7) (E 7))
       (anticommutes (S 8) (E 8)))))))))

def bxor (a b : Bool) : Bool := decide (a ≠ b)
def maskXor (a b : StabMask) : StabMask := fun i => bxor (a i) (b i)

def bitPauli : Bool -> Bool -> Pauli
  | false, false => .I
  | true, false => .X
  | false, true => .Z
  | true, true => .Y

def stabXBit (m : StabMask) (q : DataQ) : Bool :=
  match q.val with
  | 0 => m 4
  | 1 => xor (m 1) (m 4)
  | 2 => m 1
  | 3 => m 2
  | 4 => xor (m 1) (m 2)
  | 5 => m 1
  | 6 => m 2
  | 7 => xor (m 2) (m 7)
  | _ => m 7

def stabZBit (m : StabMask) (q : DataQ) : Bool :=
  match q.val with
  | 0 => m 0
  | 1 => m 0
  | 2 => m 5
  | 3 => xor (m 0) (m 6)
  | 4 => xor (m 0) (m 3)
  | 5 => xor (m 3) (m 5)
  | 6 => m 6
  | 7 => m 3
  | _ => m 3

def prodStab (m : StabMask) : DataPauli :=
  fun q => bitPauli (stabXBit m q) (stabZBit m q)

def pauliPow (b : Bool) (E : DataPauli) : DataPauli :=
  if b then E else dataI

def logicalXBit (E : DataPauli) : Bool :=
  xor (xor (hasX (E 3)) (hasX (E 8))) (hasX (E 7))

def logicalZBit (E : DataPauli) : Bool :=
  xor (xor (hasZ (E 1)) (hasZ (E 6))) (hasZ (E 3))

def centralizerMask (E : DataPauli) (i : StabIdx) : Bool :=
  match i.val with
  | 0 => xor (hasZ (E 1)) (logicalZBit E)
  | 1 => hasX (E 2)
  | 2 => xor (hasX (E 3)) (logicalXBit E)
  | 3 => hasZ (E 8)
  | 4 => xor (hasX (E 1)) (hasX (E 2))
  | 5 => xor (hasZ (E 2)) (logicalZBit E)
  | 6 => hasZ (E 6)
  | _ => hasX (E 8)

def centralizerNFOf (m : StabMask) (lx lz : Bool) : DataPauli :=
  fun q =>
    bitPauli
      (xor (stabXBit m q) (if lx then hasX (logicalX q) else false))
      (xor (stabZBit m q) (if lz then hasZ (logicalZ q) else false))

def centralizerNF (E : DataPauli) : DataPauli :=
  centralizerNFOf (centralizerMask E) (logicalXBit E) (logicalZBit E)

def centralizerGen (m : Fin 1024) : DataPauli :=
  let sm : StabMask := fun i => Nat.testBit m.val i.val
  let withX := if Nat.testBit m.val 8 then pmul (prodStab sm) logicalX else prodStab sm
  if Nat.testBit m.val 9 then pmul withX logicalZ else withX

def rowOf (q : DataQ) : RowCol := ⟨q.val / 3, by omega⟩
def colOf (q : DataQ) : RowCol := ⟨q.val % 3, Nat.mod_lt _ (by decide : 0 < 3)⟩

def rowHasXb (E : DataPauli) (r : RowCol) : Bool :=
  match r.val with
  | 0 => hasX (E 0) || hasX (E 1) || hasX (E 2)
  | 1 => hasX (E 3) || hasX (E 4) || hasX (E 5)
  | _ => hasX (E 6) || hasX (E 7) || hasX (E 8)

def colHasZb (E : DataPauli) (c : RowCol) : Bool :=
  match c.val with
  | 0 => hasZ (E 0) || hasZ (E 3) || hasZ (E 6)
  | 1 => hasZ (E 1) || hasZ (E 4) || hasZ (E 7)
  | _ => hasZ (E 2) || hasZ (E 5) || hasZ (E 8)

def RowHasX (E : DataPauli) (r : RowCol) : Prop :=
  rowHasXb E r = true

def ColHasZ (E : DataPauli) (c : RowCol) : Prop :=
  colHasZb E c = true

instance instDecidableRowHasX (E : DataPauli) (r : RowCol) : Decidable (RowHasX E r) := by
  unfold RowHasX
  infer_instance

instance instDecidableColHasZ (E : DataPauli) (c : RowCol) : Decidable (ColHasZ E c) := by
  unfold ColHasZ
  infer_instance

def bcount3 (a b c : Bool) : Nat :=
  (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)

def rowSpreadX (E : DataPauli) : Nat :=
  bcount3 (rowHasXb E 0) (rowHasXb E 1) (rowHasXb E 2)

def colSpreadZ (E : DataPauli) : Nat :=
  bcount3 (colHasZb E 0) (colHasZb E 1) (colHasZb E 2)

def XRowsLe (E : DataPauli) (f : Nat) : Prop :=
  ((Finset.univ.filter fun m : StabMask => rowSpreadX (pmul (prodStab m) E) ≤ f).card > 0)

def ZColsLe (E : DataPauli) (f : Nat) : Prop :=
  ((Finset.univ.filter fun m : StabMask => colSpreadZ (pmul (prodStab m) E) ≤ f).card > 0)

def BI_PAIR (E : DataPauli) (f : Nat) : Prop :=
  XRowsLe E f ∧ ZColsLe E f

def Centralizer (E : DataPauli) : Prop :=
  ∀ i : StabIdx, parity (stabAt i) E = false

def Stab (E : DataPauli) : Prop :=
  ((Finset.univ.filter fun m : StabMask => E = prodStab m).card > 0)

def LogicalAny (E : DataPauli) : Prop :=
  Centralizer E ∧ ¬ Stab E

def ZeroDet (d : DetVec) : Prop :=
  ∀ i : StabIdx, d i = false

instance instDecidableXRowsLe (E : DataPauli) (f : Nat) : Decidable (XRowsLe E f) := by
  unfold XRowsLe
  infer_instance

instance instDecidableZColsLe (E : DataPauli) (f : Nat) : Decidable (ZColsLe E f) := by
  unfold ZColsLe
  infer_instance

instance instDecidableBIPair (E : DataPauli) (f : Nat) : Decidable (BI_PAIR E f) := by
  unfold BI_PAIR
  infer_instance

instance instDecidableCentralizer (E : DataPauli) : Decidable (Centralizer E) := by
  unfold Centralizer
  infer_instance

instance instDecidableStab (E : DataPauli) : Decidable (Stab E) := by
  unfold Stab
  infer_instance

instance instDecidableLogicalAny (E : DataPauli) : Decidable (LogicalAny E) := by
  unfold LogicalAny
  infer_instance

instance instDecidableZeroDet (d : DetVec) : Decidable (ZeroDet d) := by
  unfold ZeroDet
  infer_instance

inductive GateOp where
  | prep0 (q : PhysQ)
  | prepP (q : PhysQ)
  | h (q : PhysQ)
  | cx (control target : PhysQ)
  | measZ (q : PhysQ)
  deriving DecidableEq, Repr

inductive IOp where
  | fault (q : PhysQ)
  | gate (g : GateOp)
  deriving DecidableEq, Repr

def mapGate (g : GateOp) (E : PhysPauli) : PhysPauli :=
  match g with
  | .prep0 q => fun i => if i = q then .I else E i
  | .prepP q => fun i => if i = q then .I else E i
  | .h q => fun i => if i = q then hadamardAction (E i) else E i
  | .measZ q => fun i => if i = q then .I else E i
  | .cx c t =>
      fun i =>
        if i = t then Pauli.mul (xPart (E c)) (E t)
        else if i = c then Pauli.mul (zPart (E t)) (E c)
        else E i

def PropDet : List GateOp -> PhysPauli -> PhysPauli
  | [], E => E
  | g :: gs, E => PropDet gs (mapGate g E)

def dataOf (E : PhysPauli) : DataPauli :=
  fun q => E ⟨q.val, by omega⟩

def deterministicSuffix : List IOp -> List GateOp
  | [] => []
  | .fault _ :: xs => deterministicSuffix xs
  | .gate g :: xs => g :: deterministicSuffix xs

structure FaultSite where
  q : PhysQ
  suffix : List GateOp
  deriving DecidableEq, Repr

def faultSitesOf : List IOp -> List FaultSite
  | [] => []
  | .fault q :: xs => { q := q, suffix := deterministicSuffix xs } :: faultSitesOf xs
  | .gate _ :: xs => faultSitesOf xs

def zGadget (order : List PhysQ) : List IOp :=
  [.fault (pq 9), .gate (.prep0 (pq 9))] ++
  (order.map (fun q => [.fault q, .fault (pq 9), .gate (.cx q (pq 9))])).flatten ++
  [.fault (pq 9), .gate (.measZ (pq 9))]

def xGadget (order : List PhysQ) : List IOp :=
  [.fault (pq 9), .gate (.prepP (pq 9))] ++
  (order.map (fun q => [.fault (pq 9), .fault q, .gate (.cx (pq 9) q)])).flatten ++
  [.fault (pq 9), .gate (.h (pq 9)), .fault (pq 9), .gate (.measZ (pq 9))]

def G0 : List IOp := zGadget [pq 0, pq 3, pq 1, pq 4]
def G1 : List IOp := xGadget [pq 1, pq 2, pq 4, pq 5]
def G2 : List IOp := xGadget [pq 3, pq 4, pq 6, pq 7]
def G3 : List IOp := zGadget [pq 4, pq 7, pq 5, pq 8]
def G4 : List IOp := xGadget [pq 0, pq 1]
def G5 : List IOp := zGadget [pq 2, pq 5]
def G6 : List IOp := zGadget [pq 3, pq 6]
def G7 : List IOp := xGadget [pq 7, pq 8]

def C_NZ_D3_prog : List IOp :=
  G0 ++ (G1 ++ (G2 ++ (G3 ++ (G4 ++ (G5 ++ (G6 ++ G7))))))

def C_NZ_D3_sites : List FaultSite :=
  ([G0, G1, G2, G3, G4, G5, G6, G7].map faultSitesOf).flatten

inductive FaultBranch where
  | X | Y | Z
  deriving DecidableEq, Repr, Fintype

def FaultBranch.toPauli : FaultBranch -> Pauli
  | .X => .X
  | .Y => .Y
  | .Z => .Z

def faultDelta (site : FaultSite) (b : FaultBranch) : DataPauli :=
  dataOf (PropDet site.suffix (singlePhys site.q b.toPauli))

def DeltaSafe (D : DataPauli) : Prop :=
  XRowsLe D 1 ∧ ZColsLe D 1

def SiteSafe (site : FaultSite) : Prop :=
  ∀ b : FaultBranch, DeltaSafe (faultDelta site b)

inductive Exec : List IOp -> PhysPauli -> Nat -> PhysPauli -> Nat -> Prop where
  | nil (phys : PhysPauli) (faults : Nat) : Exec [] phys faults phys faults
  | gate {g rest phys faults phys' faults'} :
      Exec rest (mapGate g phys) faults phys' faults' ->
      Exec (.gate g :: rest) phys faults phys' faults'
  | faultNone {q rest phys faults phys' faults'} :
      Exec rest phys faults phys' faults' ->
      Exec (.fault q :: rest) phys faults phys' faults'
  | faultSome {q rest phys faults phys' faults'} (b : FaultBranch) :
      Exec rest (phMul phys (singlePhys q b.toPauli)) (faults + 1) phys' faults' ->
      Exec (.fault q :: rest) phys faults phys' faults'

instance instDecidableDeltaSafe (D : DataPauli) : Decidable (DeltaSafe D) := by
  unfold DeltaSafe
  infer_instance

instance instDecidableSiteSafe (site : FaultSite) : Decidable (SiteSafe site) := by
  unfold SiteSafe
  infer_instance

theorem bxor_eq_xor (a b : Bool) : bxor a b = xor a b := by
  cases a <;> cases b <;> rfl

theorem bitPauli_mul (ax az bx bz : Bool) :
    bitPauli (xor ax bx) (xor az bz) =
      Pauli.mul (bitPauli ax az) (bitPauli bx bz) := by
  cases ax <;> cases az <;> cases bx <;> cases bz <;> rfl

theorem hasX_bitPauli_mul (ax az bx bz : Bool) :
    hasX (Pauli.mul (bitPauli ax az) (bitPauli bx bz)) = xor ax bx := by
  cases ax <;> cases az <;> cases bx <;> cases bz <;> rfl

theorem hasZ_bitPauli_mul (ax az bx bz : Bool) :
    hasZ (Pauli.mul (bitPauli ax az) (bitPauli bx bz)) = xor az bz := by
  cases ax <;> cases az <;> cases bx <;> cases bz <;> rfl

theorem xor_pair_swap (a b c d : Bool) :
    xor (xor a b) (xor c d) = xor (xor a c) (xor b d) := by
  change (a + b) + (c + d) = (a + c) + (b + d)
  ring

theorem bne_xor_right (a b c : Bool) : (b != (a ^^ c)) = (a != (b ^^ c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem stabXBit_maskXor (a b : StabMask) (q : DataQ) :
    stabXBit (maskXor a b) q = xor (stabXBit a q) (stabXBit b q) := by
  fin_cases q <;> simp [stabXBit, maskXor, bxor_eq_xor, bne_xor_right]

theorem stabZBit_maskXor (a b : StabMask) (q : DataQ) :
    stabZBit (maskXor a b) q = xor (stabZBit a q) (stabZBit b q) := by
  fin_cases q <;> simp [stabZBit, maskXor, bxor_eq_xor, bne_xor_right]

theorem prodStab_xor :
    ∀ a b : StabMask, prodStab (maskXor a b) = pmul (prodStab a) (prodStab b) := by
  intro a b
  funext q
  simp [prodStab, pmul, stabXBit_maskXor, stabZBit_maskXor, bitPauli_mul]

theorem pmul_assoc (A B C : DataPauli) : pmul (pmul A B) C = pmul A (pmul B C) := by
  funext q
  exact Pauli.mul_assoc (A q) (B q) (C q)

theorem pmul_comm (A B : DataPauli) : pmul A B = pmul B A := by
  funext q
  let a := A q
  let b := B q
  change Pauli.mul a b = Pauli.mul b a
  cases a <;> cases b <;> rfl

theorem phMul_comm (A B : PhysPauli) : phMul A B = phMul B A := by
  funext q
  let a := A q
  let b := B q
  change Pauli.mul a b = Pauli.mul b a
  cases a <;> cases b <;> rfl

theorem dataOf_phMul (A B : PhysPauli) :
    dataOf (phMul A B) = pmul (dataOf A) (dataOf B) := by
  rfl

theorem mapGate_phMul (g : GateOp) (A B : PhysPauli) :
    mapGate g (phMul A B) = phMul (mapGate g A) (mapGate g B) := by
  cases g with
  | prep0 q =>
      funext i
      by_cases h : i = q <;> simp [mapGate, phMul, h]
      rfl
  | prepP q =>
      funext i
      by_cases h : i = q <;> simp [mapGate, phMul, h]
      rfl
  | h q =>
      funext i
      by_cases hq : i = q
      · simp [mapGate, phMul, hq]
        cases A q <;> cases B q <;> rfl
      · simp [mapGate, phMul, hq]
  | measZ q =>
      funext i
      by_cases h : i = q <;> simp [mapGate, phMul, h]
      rfl
  | cx c t =>
      funext i
      by_cases ht : i = t
      · simp [mapGate, phMul, ht]
        cases A c <;> cases B c <;> cases A t <;> cases B t <;> rfl
      · by_cases hc : i = c
        · simp [mapGate, phMul, hc]
          have hct : c ≠ t := by
            intro h
            exact ht (by simpa [h] using hc)
          simp [hct]
          cases A t <;> cases B t <;> cases A c <;> cases B c <;> rfl
        · simp [mapGate, phMul, ht, hc]

theorem PropDet_phMul :
    ∀ (suffix : List GateOp) (A B : PhysPauli),
      PropDet suffix (phMul A B) = phMul (PropDet suffix A) (PropDet suffix B)
  | [], A, B => rfl
  | g :: gs, A, B => by
      simp [PropDet, mapGate_phMul, PropDet_phMul gs (mapGate g A) (mapGate g B)]

theorem mapGate_physI (g : GateOp) : mapGate g physI = physI := by
  cases g with
  | prep0 q =>
      funext i
      by_cases h : i = q <;> simp [mapGate, physI, h]
  | prepP q =>
      funext i
      by_cases h : i = q <;> simp [mapGate, physI, h]
  | h q =>
      funext i
      by_cases hq : i = q <;> simp [mapGate, physI, hq, hadamardAction]
  | measZ q =>
      funext i
      by_cases h : i = q <;> simp [mapGate, physI, h]
  | cx c t =>
      funext i
      by_cases ht : i = t
      · simp [mapGate, physI, ht, xPart]
        rfl
      · by_cases hc : i = c
        · have hct : c ≠ t := by
            intro h
            exact ht (by simpa [h] using hc)
          simp [mapGate, physI, hc, hct, zPart]
          rfl
        · simp [mapGate, physI, ht, hc]

theorem PropDet_physI : ∀ suffix : List GateOp, PropDet suffix physI = physI
  | [] => rfl
  | g :: gs => by
      simp [PropDet, mapGate_physI g, PropDet_physI gs]

theorem PropDet_append :
    ∀ (a b : List GateOp) (E : PhysPauli),
      PropDet (a ++ b) E = PropDet b (PropDet a E)
  | [], b, E => rfl
  | g :: gs, b, E => by
      simp [PropDet, PropDet_append gs b (mapGate g E)]

def anc : PhysQ := pq 9

def zCNOTs (order : List PhysQ) : List GateOp :=
  order.map (fun q => GateOp.cx q anc)

def xCNOTs (order : List PhysQ) : List GateOp :=
  order.map (fun q => GateOp.cx anc q)

def zNoZ (E : PhysPauli) : Prop := zPart (E anc) = .I
def xNoX (E : PhysPauli) : Prop := xPart (E anc) = .I

theorem dataPhys_ne_anc (q : DataQ) :
    (⟨q.val, by omega⟩ : PhysQ) ≠ anc := by
  intro h
  have hv := congrArg Fin.val h
  simp [anc, pq] at hv
  omega

theorem dataOf_prep0_anc (E : PhysPauli) :
    dataOf (mapGate (.prep0 anc) E) = dataOf E := by
  funext q
  have hne := dataPhys_ne_anc q
  simp [dataOf, mapGate, hne]

theorem dataOf_prepP_anc (E : PhysPauli) :
    dataOf (mapGate (.prepP anc) E) = dataOf E := by
  funext q
  have hne := dataPhys_ne_anc q
  simp [dataOf, mapGate, hne]

theorem dataOf_h_anc (E : PhysPauli) :
    dataOf (mapGate (.h anc) E) = dataOf E := by
  funext q
  have hne := dataPhys_ne_anc q
  simp [dataOf, mapGate, hne]

theorem dataOf_measZ_anc (E : PhysPauli) :
    dataOf (mapGate (.measZ anc) E) = dataOf E := by
  funext q
  have hne := dataPhys_ne_anc q
  simp [dataOf, mapGate, hne]

theorem zNoZ_prep0_anc (E : PhysPauli) : zNoZ (mapGate (.prep0 anc) E) := by
  simp [zNoZ, anc, mapGate, zPart]

theorem xNoX_prepP_anc (E : PhysPauli) : xNoX (mapGate (.prepP anc) E) := by
  simp [xNoX, anc, mapGate, xPart]

theorem dataOf_cx_data_to_anc (q : PhysQ) (E : PhysPauli) (hZ : zNoZ E) :
    dataOf (mapGate (.cx q anc) E) = dataOf E := by
  funext d
  change (mapGate (.cx q anc) E) (⟨d.val, by omega⟩ : PhysQ) =
    E (⟨d.val, by omega⟩ : PhysQ)
  have hne : (⟨d.val, by omega⟩ : PhysQ) ≠ anc := dataPhys_ne_anc d
  by_cases hc : (⟨d.val, by omega⟩ : PhysQ) = q
  · unfold zNoZ at hZ
    simp [anc] at hZ
    have hqne : q ≠ anc := by
      intro hq
      exact hne (by simp [hc, hq])
    have hqne' : q ≠ pq 9 := by simpa [anc] using hqne
    simp [mapGate, hc, hqne', hZ, anc]
    cases E (⟨d.val, by omega⟩ : PhysQ) <;> rfl
  · simp [mapGate, hne, hc]

theorem zNoZ_cx_data_to_anc (q : PhysQ) (E : PhysPauli) (hZ : zNoZ E) :
    zNoZ (mapGate (.cx q anc) E) := by
  unfold zNoZ at hZ ⊢
  simp [anc] at hZ ⊢
  cases hAnc : E (pq 9) <;> simp [hAnc, zPart] at hZ
  · cases hqv : E q <;> simp [mapGate, hqv, hAnc, xPart, zPart, Pauli.mul]
  · cases hqv : E q <;> simp [mapGate, hqv, hAnc, xPart, zPart, Pauli.mul]

theorem dataOf_cx_anc_to_data (q : PhysQ) (E : PhysPauli) (hX : xNoX E) :
    dataOf (mapGate (.cx anc q) E) = dataOf E := by
  funext d
  change (mapGate (.cx anc q) E) (⟨d.val, by omega⟩ : PhysQ) =
    E (⟨d.val, by omega⟩ : PhysQ)
  have hne : (⟨d.val, by omega⟩ : PhysQ) ≠ anc := dataPhys_ne_anc d
  by_cases ht : (⟨d.val, by omega⟩ : PhysQ) = q
  · unfold xNoX at hX
    simp [anc] at hX
    simp [mapGate, ht, hX, anc]
    cases E (⟨d.val, by omega⟩ : PhysQ) <;> rfl
  · simp [mapGate, hne, ht]

theorem xNoX_cx_anc_to_data (q : PhysQ) (E : PhysPauli) (hq : q ≠ anc)
    (hX : xNoX E) :
    xNoX (mapGate (.cx anc q) E) := by
  unfold xNoX at hX ⊢
  simp [anc] at hX ⊢
  have hqt : pq 9 ≠ q := by
    simpa [anc] using (Ne.symm hq)
  cases hAnc : E (pq 9) <;> simp [hAnc, xPart] at hX
  · cases hqv : E q <;> simp [mapGate, hqt, hqv, hAnc, xPart, zPart, Pauli.mul]
  · cases hqv : E q <;> simp [mapGate, hqt, hqv, hAnc, xPart, zPart, Pauli.mul]

theorem dataOf_zCNOTs :
    ∀ (order : List PhysQ) (E : PhysPauli),
      (∀ q, q ∈ order -> q ≠ anc) ->
      zNoZ E ->
      dataOf (PropDet (zCNOTs order) E) = dataOf E ∧
        zNoZ (PropDet (zCNOTs order) E)
  | [], E, _, hZ => by
      simp [zCNOTs, PropDet, hZ]
  | q :: qs, E, hOrder, hZ => by
      have hTail : ∀ r, r ∈ qs -> r ≠ anc := by
        intro r hr
        exact hOrder r (by simp [hr])
      have hStepData := dataOf_cx_data_to_anc q E hZ
      have hStepZ := zNoZ_cx_data_to_anc q E hZ
      rcases dataOf_zCNOTs qs (mapGate (.cx q anc) E) hTail hStepZ with
        ⟨hDataTail, hZTail⟩
      constructor
      · simp [zCNOTs, PropDet]
        exact hDataTail.trans hStepData
      · simpa [zCNOTs, PropDet] using hZTail

theorem dataOf_xCNOTs :
    ∀ (order : List PhysQ) (E : PhysPauli),
      (∀ q, q ∈ order -> q ≠ anc) ->
      xNoX E ->
      dataOf (PropDet (xCNOTs order) E) = dataOf E ∧
        xNoX (PropDet (xCNOTs order) E)
  | [], E, _, hX => by
      simp [xCNOTs, PropDet, hX]
  | q :: qs, E, hOrder, hX => by
      have hq : q ≠ anc := hOrder q (by simp)
      have hTail : ∀ r, r ∈ qs -> r ≠ anc := by
        intro r hr
        exact hOrder r (by simp [hr])
      have hStepData := dataOf_cx_anc_to_data q E hX
      have hStepX := xNoX_cx_anc_to_data q E hq hX
      rcases dataOf_xCNOTs qs (mapGate (.cx anc q) E) hTail hStepX with
        ⟨hDataTail, hXTail⟩
      constructor
      · simp [xCNOTs, PropDet]
        exact hDataTail.trans hStepData
      · simpa [xCNOTs, PropDet] using hXTail

theorem deterministicSuffix_zGadget_tail (order : List PhysQ) :
    deterministicSuffix
      ((order.map (fun q => [.fault q, .fault anc, .gate (.cx q anc)])).flatten ++
        [.fault anc, .gate (.measZ anc)]) =
      zCNOTs order ++ [.measZ anc] := by
  induction order with
  | nil =>
      simp [zCNOTs, deterministicSuffix, anc]
  | cons q qs ih =>
      simp [anc] at ih
      simp [zCNOTs, deterministicSuffix, ih, anc]

theorem deterministicSuffix_xGadget_tail (order : List PhysQ) :
    deterministicSuffix
      ((order.map (fun q => [.fault anc, .fault q, .gate (.cx anc q)])).flatten ++
        [.fault anc, .gate (.h anc), .fault anc, .gate (.measZ anc)]) =
      xCNOTs order ++ [.h anc, .measZ anc] := by
  induction order with
  | nil =>
      simp [xCNOTs, deterministicSuffix, anc]
  | cons q qs ih =>
      simp [anc] at ih
      simp [xCNOTs, deterministicSuffix, ih, anc]

theorem deterministicSuffix_zGadget (order : List PhysQ) :
    deterministicSuffix (zGadget order) =
      .prep0 anc :: zCNOTs order ++ [.measZ anc] := by
  unfold zGadget
  simp [deterministicSuffix]
  simpa [anc] using deterministicSuffix_zGadget_tail order

theorem deterministicSuffix_xGadget (order : List PhysQ) :
    deterministicSuffix (xGadget order) =
      .prepP anc :: xCNOTs order ++ [.h anc, .measZ anc] := by
  unfold xGadget
  simp [deterministicSuffix]
  simpa [anc] using deterministicSuffix_xGadget_tail order

theorem dataOf_det_zGadget (order : List PhysQ) (E : PhysPauli)
    (hOrder : ∀ q, q ∈ order -> q ≠ anc) :
    dataOf (PropDet (deterministicSuffix (zGadget order)) E) = dataOf E := by
  rw [deterministicSuffix_zGadget]
  change dataOf (PropDet (zCNOTs order ++ [.measZ anc])
    (mapGate (.prep0 anc) E)) = dataOf E
  rw [PropDet_append]
  rcases dataOf_zCNOTs order (mapGate (.prep0 anc) E) hOrder
      (zNoZ_prep0_anc E) with ⟨hData, _⟩
  calc
    dataOf (PropDet [.measZ anc] (PropDet (zCNOTs order) (mapGate (.prep0 anc) E))) =
        dataOf (PropDet (zCNOTs order) (mapGate (.prep0 anc) E)) := by
          simp [PropDet, dataOf_measZ_anc]
    _ = dataOf (mapGate (.prep0 anc) E) := hData
    _ = dataOf E := dataOf_prep0_anc E

theorem dataOf_det_xGadget (order : List PhysQ) (E : PhysPauli)
    (hOrder : ∀ q, q ∈ order -> q ≠ anc) :
    dataOf (PropDet (deterministicSuffix (xGadget order)) E) = dataOf E := by
  rw [deterministicSuffix_xGadget]
  change dataOf (PropDet (xCNOTs order ++ [.h anc, .measZ anc])
    (mapGate (.prepP anc) E)) = dataOf E
  rw [PropDet_append]
  rcases dataOf_xCNOTs order (mapGate (.prepP anc) E) hOrder
      (xNoX_prepP_anc E) with ⟨hData, _⟩
  calc
    dataOf (PropDet [.h anc, .measZ anc]
        (PropDet (xCNOTs order) (mapGate (.prepP anc) E))) =
        dataOf (PropDet (xCNOTs order) (mapGate (.prepP anc) E)) := by
          simp [PropDet, dataOf_h_anc, dataOf_measZ_anc]
    _ = dataOf (mapGate (.prepP anc) E) := hData
    _ = dataOf E := dataOf_prepP_anc E

theorem bitPauli_hasX_hasZ (p : Pauli) : bitPauli (hasX p) (hasZ p) = p := by
  cases p <;> rfl

theorem anticommutes_Z (p : Pauli) : anticommutes .Z p = hasX p := by
  cases p <;> rfl

theorem anticommutes_X (p : Pauli) : anticommutes .X p = hasZ p := by
  cases p <;> rfl

theorem anticommutes_I_left (p : Pauli) : anticommutes .I p = false := by
  rfl

theorem bitPauli_eq_iff (x₁ z₁ x₂ z₂ : Bool) :
    bitPauli x₁ z₁ = bitPauli x₂ z₂ ↔ x₁ = x₂ ∧ z₁ = z₂ := by
  cases x₁ <;> cases z₁ <;> cases x₂ <;> cases z₂ <;> simp [bitPauli]

theorem bool_false_of_not_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp at h ⊢

theorem bit_nf_x0 (x0 x1 x2 x3 x4 x5 x7 x8 : Bool)
    (h0 : x0 = xor x1 (xor x3 x4))
    (h3 : x4 = xor x5 (xor x7 x8))
    (h5 : x2 = x5) :
    x0 = xor (xor x1 x2) (xor (xor x3 x8) x7) := by
  decide +revert

theorem bit_nf_z0 (z0 z1 z3 z6 : Bool) (h4 : z0 = z1) :
    z0 = xor (xor z1 (xor (xor z1 z6) z3)) (xor (xor z1 z6) z3) := by
  decide +revert

theorem bit_nf_x1 (x1 x2 : Bool) :
    x1 = xor x2 (xor x1 x2) := by
  decide +revert

theorem bit_nf_z1 (z1 z3 z6 : Bool) :
    z1 = xor (xor z1 (xor (xor z1 z6) z3)) (xor (xor z1 z6) z3) := by
  decide +revert

theorem bit_nf_z2 (z1 z2 z3 z6 : Bool) :
    z2 = xor (xor z2 (xor (xor z1 z6) z3)) (xor (xor z1 z6) z3) := by
  decide +revert

theorem bit_nf_x3 (x3 x7 x8 : Bool) :
    x3 = xor (xor x3 (xor (xor x3 x8) x7)) (xor (xor x3 x8) x7) := by
  decide +revert

theorem bit_nf_z3 (z1 z3 z6 : Bool) :
    z3 = xor (xor z1 (xor (xor z1 z6) z3)) z6 := by
  decide +revert

theorem bit_nf_x4 (x2 x3 x4 x5 x7 x8 : Bool)
    (h3 : x4 = xor x5 (xor x7 x8))
    (h5 : x2 = x5) :
    x4 = xor x2 (xor x3 (xor (xor x3 x8) x7)) := by
  decide +revert

theorem bit_nf_z4 (z1 z3 z4 z6 z7 z8 : Bool)
    (h2 : z3 = xor z4 (xor z6 z7))
    (h7 : z7 = z8) :
    z4 = xor (xor z1 (xor (xor z1 z6) z3)) z8 := by
  decide +revert

theorem bit_nf_x5 (x2 x5 : Bool) (h5 : x2 = x5) :
    x5 = x2 := by
  decide +revert

theorem bit_nf_z5 (z1 z2 z3 z4 z5 z6 z7 z8 : Bool)
    (h1 : z1 = xor z2 (xor z4 z5))
    (h2 : z3 = xor z4 (xor z6 z7))
    (h7 : z7 = z8) :
    z5 = xor z8 (xor z2 (xor (xor z1 z6) z3)) := by
  decide +revert

theorem bit_nf_x6 (x3 x6 x7 x8 : Bool) (h6 : x3 = x6) :
    x6 = xor (xor x3 (xor (xor x3 x8) x7)) (xor (xor x3 x8) x7) := by
  decide +revert

theorem bit_nf_x7 (x3 x7 x8 : Bool) :
    x7 = xor (xor x3 (xor (xor x3 x8) x7)) x8 := by
  decide +revert

theorem bool_ite_true_false (b : Bool) : (if b then true else false) = b := by
  cases b <;> rfl

theorem bool_ite_false_false (b : Bool) : (if b then false else false) = false := by
  cases b <;> rfl

theorem bool_ite_eq_true_true_false (b : Bool) :
    (if b = true then true else false) = b := by
  cases b <;> rfl

theorem bool_ite_eq_true_false_false (b : Bool) :
    (if b = true then false else false) = false := by
  cases b <;> rfl

theorem xor_false_right (b : Bool) : xor b false = b := by
  cases b <;> rfl

@[simp] theorem hasX_logicalX (q : DataQ) :
    hasX (logicalX q) =
      match q.val with
      | 0 | 3 | 6 => true
      | _ => false := by
  fin_cases q <;> rfl

@[simp] theorem hasZ_logicalZ (q : DataQ) :
    hasZ (logicalZ q) =
      match q.val with
      | 0 | 1 | 2 => true
      | _ => false := by
  fin_cases q <;> rfl

theorem centralizerNFOf_stab (m : StabMask) :
    centralizerNFOf m false false = prodStab m := by
  funext q
  simp [centralizerNFOf, prodStab]

theorem centralizer_normal_form (E : DataPauli) :
    Centralizer E -> E = centralizerNF E := by
  intro h
  have h0 := h (⟨0, by decide⟩)
  have h1 := h (⟨1, by decide⟩)
  have h2 := h (⟨2, by decide⟩)
  have h3 := h (⟨3, by decide⟩)
  have h4 := h (⟨4, by decide⟩)
  have h5 := h (⟨5, by decide⟩)
  have h6 := h (⟨6, by decide⟩)
  have h7 := h (⟨7, by decide⟩)
  simp [parity, stabAt, s0, s1, s2, s3, s4, s5, s6, s7,
    anticommutes_Z, anticommutes_X, anticommutes_I_left] at h0 h1 h2 h3 h4 h5 h6 h7
  have hx0 := bit_nf_x0
    (hasX (E 0)) (hasX (E 1)) (hasX (E 2))
    (hasX (E 3)) (hasX (E 4)) (hasX (E 5))
    (hasX (E 7)) (hasX (E 8)) h0 h3 h5
  have hz0 := bit_nf_z0
    (hasZ (E 0)) (hasZ (E 1)) (hasZ (E 3))
    (hasZ (E 6)) h4
  have hx1 := bit_nf_x1 (hasX (E 1)) (hasX (E 2))
  have hz1 := bit_nf_z1
    (hasZ (E 1)) (hasZ (E 3)) (hasZ (E 6))
  have hx2 : hasX (E 2) = hasX (E 2) := rfl
  have hz2 := bit_nf_z2
    (hasZ (E 1)) (hasZ (E 2)) (hasZ (E 3))
    (hasZ (E 6))
  have hx3 := bit_nf_x3
    (hasX (E 3)) (hasX (E 7)) (hasX (E 8))
  have hz3 := bit_nf_z3
    (hasZ (E 1)) (hasZ (E 3)) (hasZ (E 6))
  have hx4 := bit_nf_x4
    (hasX (E 2)) (hasX (E 3)) (hasX (E 4))
    (hasX (E 5)) (hasX (E 7)) (hasX (E 8)) h3 h5
  have hz4 := bit_nf_z4
    (hasZ (E 1)) (hasZ (E 3)) (hasZ (E 4))
    (hasZ (E 6)) (hasZ (E 7)) (hasZ (E 8)) h2 h7
  have hx5 := bit_nf_x5 (hasX (E 2)) (hasX (E 5)) h5
  have hz5 := bit_nf_z5
    (hasZ (E 1)) (hasZ (E 2)) (hasZ (E 3))
    (hasZ (E 4)) (hasZ (E 5)) (hasZ (E 6))
    (hasZ (E 7)) (hasZ (E 8)) h1 h2 h7
  have hx6 := bit_nf_x6
    (hasX (E 3)) (hasX (E 6)) (hasX (E 7))
    (hasX (E 8)) h6
  have hz6 : hasZ (E 6) = hasZ (E 6) := rfl
  have hx7 := bit_nf_x7
    (hasX (E 3)) (hasX (E 7)) (hasX (E 8))
  have hz7 := h7
  have hx8 : hasX (E 8) = hasX (E 8) := rfl
  have hz8 : hasZ (E 8) = hasZ (E 8) := rfl
  funext q
  rw [← bitPauli_hasX_hasZ (E q)]
  fin_cases q <;>
    unfold centralizerNF centralizerNFOf <;>
    apply (bitPauli_eq_iff _ _ _ _).mpr <;>
    constructor <;>
    simp only [centralizerMask, logicalXBit, logicalZBit, stabXBit, stabZBit,
      bool_ite_true_false, bool_ite_false_false, xor_false_right,
      hasX_logicalX, hasZ_logicalZ]
  all_goals first
    | exact hx0
    | exact hz0
    | exact hx1
    | exact hz1
    | exact hx2
    | exact hz2
    | exact hx3
    | exact hz3
    | exact hx4
    | exact hz4
    | exact hx5
    | exact hz5
    | exact hx6
    | exact hz6
    | exact hx7
    | exact hz7
    | exact hx8
    | exact hz8

theorem hasX_mul_true {a b : Pauli} :
    hasX (Pauli.mul a b) = true -> hasX a = true ∨ hasX b = true := by
  cases a <;> cases b <;> simp [hasX, Pauli.mul]

theorem hasZ_mul_true {a b : Pauli} :
    hasZ (Pauli.mul a b) = true -> hasZ a = true ∨ hasZ b = true := by
  cases a <;> cases b <;> simp [hasZ, Pauli.mul]

theorem or3_hasX_mul_true {a0 a1 a2 b0 b1 b2 : Pauli} :
    (hasX (Pauli.mul a0 b0) || hasX (Pauli.mul a1 b1) ||
        hasX (Pauli.mul a2 b2)) = true ->
      (hasX a0 || hasX a1 || hasX a2) = true ∨
        (hasX b0 || hasX b1 || hasX b2) = true := by
  cases a0 <;> cases a1 <;> cases a2 <;>
    cases b0 <;> cases b1 <;> cases b2 <;>
    simp [hasX, Pauli.mul]

theorem or3_hasZ_mul_true {a0 a1 a2 b0 b1 b2 : Pauli} :
    (hasZ (Pauli.mul a0 b0) || hasZ (Pauli.mul a1 b1) ||
        hasZ (Pauli.mul a2 b2)) = true ->
      (hasZ a0 || hasZ a1 || hasZ a2) = true ∨
        (hasZ b0 || hasZ b1 || hasZ b2) = true := by
  cases a0 <;> cases a1 <;> cases a2 <;>
    cases b0 <;> cases b1 <;> cases b2 <;>
    simp [hasZ, Pauli.mul]

theorem RowHasX_pmul {A B : DataPauli} {r : RowCol} :
    RowHasX (pmul A B) r -> RowHasX A r ∨ RowHasX B r := by
  unfold RowHasX
  fin_cases r <;>
    intro h <;>
    exact or3_hasX_mul_true (by simpa [rowHasXb, pmul] using h)

theorem ColHasZ_pmul {A B : DataPauli} {c : RowCol} :
    ColHasZ (pmul A B) c -> ColHasZ A c ∨ ColHasZ B c := by
  unfold ColHasZ
  fin_cases c <;>
    intro h <;>
    exact or3_hasZ_mul_true (by simpa [colHasZb, pmul] using h)

theorem bcount3_le_add
    {c0 c1 c2 a0 a1 a2 b0 b1 b2 : Bool}
    (h0 : c0 = true -> a0 = true ∨ b0 = true)
    (h1 : c1 = true -> a1 = true ∨ b1 = true)
    (h2 : c2 = true -> a2 = true ∨ b2 = true) :
    bcount3 c0 c1 c2 ≤ bcount3 a0 a1 a2 + bcount3 b0 b1 b2 := by
  cases c0 <;> cases c1 <;> cases c2 <;>
    cases a0 <;> cases a1 <;> cases a2 <;>
    cases b0 <;> cases b1 <;> cases b2 <;>
    simp [bcount3] at h0 h1 h2 ⊢

theorem rowSpreadX_pmul_le (A B : DataPauli) :
    rowSpreadX (pmul A B) ≤ rowSpreadX A + rowSpreadX B := by
  unfold rowSpreadX
  apply bcount3_le_add
  · exact RowHasX_pmul (A := A) (B := B) (r := 0)
  · exact RowHasX_pmul (A := A) (B := B) (r := 1)
  · exact RowHasX_pmul (A := A) (B := B) (r := 2)

theorem colSpreadZ_pmul_le (A B : DataPauli) :
    colSpreadZ (pmul A B) ≤ colSpreadZ A + colSpreadZ B := by
  unfold colSpreadZ
  apply bcount3_le_add
  · exact ColHasZ_pmul (A := A) (B := B) (c := 0)
  · exact ColHasZ_pmul (A := A) (B := B) (c := 1)
  · exact ColHasZ_pmul (A := A) (B := B) (c := 2)

theorem XRowsLe_pmul_of_safe {E D : DataPauli} {f : Nat} :
    XRowsLe E f -> XRowsLe D 1 -> XRowsLe (pmul E D) (f + 1) := by
  intro hEX hDX
  unfold XRowsLe at hEX hDX ⊢
  rcases Finset.card_pos.mp hEX with ⟨mE, hmE⟩
  rcases Finset.card_pos.mp hDX with ⟨mD, hmD⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmE hmD
  apply Finset.card_pos.mpr
  refine ⟨maskXor mE mD, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hrepr :
      pmul (prodStab (maskXor mE mD)) (pmul E D) =
        pmul (pmul (prodStab mE) E) (pmul (prodStab mD) D) := by
    calc
      pmul (prodStab (maskXor mE mD)) (pmul E D)
          = pmul (pmul (prodStab mE) (prodStab mD)) (pmul E D) := by
              rw [prodStab_xor mE mD]
      _ = pmul (pmul (prodStab mE) E) (pmul (prodStab mD) D) := by
              funext q
              let a := prodStab mE q
              let b := prodStab mD q
              let c := E q
              let d := D q
              change Pauli.mul (Pauli.mul a b) (Pauli.mul c d) =
                Pauli.mul (Pauli.mul a c) (Pauli.mul b d)
              cases a <;> cases b <;> cases c <;> cases d <;> rfl
  rw [hrepr]
  exact Nat.le_trans (rowSpreadX_pmul_le _ _) (Nat.add_le_add hmE hmD)

theorem ZColsLe_pmul_of_safe {E D : DataPauli} {f : Nat} :
    ZColsLe E f -> ZColsLe D 1 -> ZColsLe (pmul E D) (f + 1) := by
  intro hEZ hDZ
  unfold ZColsLe at hEZ hDZ ⊢
  rcases Finset.card_pos.mp hEZ with ⟨mE, hmE⟩
  rcases Finset.card_pos.mp hDZ with ⟨mD, hmD⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmE hmD
  apply Finset.card_pos.mpr
  refine ⟨maskXor mE mD, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hrepr :
      pmul (prodStab (maskXor mE mD)) (pmul E D) =
        pmul (pmul (prodStab mE) E) (pmul (prodStab mD) D) := by
    calc
      pmul (prodStab (maskXor mE mD)) (pmul E D)
          = pmul (pmul (prodStab mE) (prodStab mD)) (pmul E D) := by
              rw [prodStab_xor mE mD]
      _ = pmul (pmul (prodStab mE) E) (pmul (prodStab mD) D) := by
              funext q
              let a := prodStab mE q
              let b := prodStab mD q
              let c := E q
              let d := D q
              change Pauli.mul (Pauli.mul a b) (Pauli.mul c d) =
                Pauli.mul (Pauli.mul a c) (Pauli.mul b d)
              cases a <;> cases b <;> cases c <;> cases d <;> rfl
  rw [hrepr]
  exact Nat.le_trans (colSpreadZ_pmul_le _ _) (Nat.add_le_add hmE hmD)

theorem BI_PAIR_pmul_of_delta_safe {E D : DataPauli} {f : Nat} :
    BI_PAIR E f -> DeltaSafe D -> BI_PAIR (pmul E D) (f + 1) := by
  rintro ⟨hX, hZ⟩ ⟨hDX, hDZ⟩
  exact ⟨XRowsLe_pmul_of_safe hX hDX, ZColsLe_pmul_of_safe hZ hDZ⟩

def maskConst (n : Nat) : StabMask :=
  fun i => Nat.testBit n i.val

def firstRowMaskAux (D : DataPauli) : Nat -> Nat -> Nat
  | 0, n => n
  | fuel + 1, n =>
      if rowSpreadX (pmul (prodStab (maskConst n)) D) ≤ 1 then
        n
      else
        firstRowMaskAux D fuel (n + 1)

def firstColMaskAux (D : DataPauli) : Nat -> Nat -> Nat
  | 0, n => n
  | fuel + 1, n =>
      if colSpreadZ (pmul (prodStab (maskConst n)) D) ≤ 1 then
        n
      else
        firstColMaskAux D fuel (n + 1)

def rowMask1 (D : DataPauli) : StabMask :=
  maskConst (firstRowMaskAux D 256 0)

def colMask1 (D : DataPauli) : StabMask :=
  maskConst (firstColMaskAux D 256 0)

def DeltaSafeFast (D : DataPauli) : Prop :=
  rowSpreadX (pmul (prodStab (rowMask1 D)) D) ≤ 1 ∧
    colSpreadZ (pmul (prodStab (colMask1 D)) D) ≤ 1

instance instDecidableDeltaSafeFast (D : DataPauli) : Decidable (DeltaSafeFast D) := by
  unfold DeltaSafeFast
  infer_instance

theorem XRowsLe_of_mask {E : DataPauli} {f : Nat} (m : StabMask)
    (h : rowSpreadX (pmul (prodStab m) E) ≤ f) : XRowsLe E f := by
  unfold XRowsLe
  apply Finset.card_pos.mpr
  refine ⟨m, ?_⟩
  simp [h]

theorem ZColsLe_of_mask {E : DataPauli} {f : Nat} (m : StabMask)
    (h : colSpreadZ (pmul (prodStab m) E) ≤ f) : ZColsLe E f := by
  unfold ZColsLe
  apply Finset.card_pos.mpr
  refine ⟨m, ?_⟩
  simp [h]

theorem DeltaSafe_of_fast {D : DataPauli} :
    DeltaSafeFast D -> DeltaSafe D := by
  rintro ⟨hX, hZ⟩
  exact ⟨XRowsLe_of_mask (rowMask1 D) hX, ZColsLe_of_mask (colMask1 D) hZ⟩

theorem DeltaSafe_witness (D : DataPauli) (mx mz : Nat)
    (hX : rowSpreadX (pmul (prodStab (maskConst mx)) D) ≤ 1)
    (hZ : colSpreadZ (pmul (prodStab (maskConst mz)) D) ≤ 1) :
    DeltaSafe D := by
  exact ⟨XRowsLe_of_mask (maskConst mx) hX, ZColsLe_of_mask (maskConst mz) hZ⟩

theorem SiteSafe_of_fast {site : FaultSite} :
    (∀ b : FaultBranch, DeltaSafeFast (faultDelta site b)) -> SiteSafe site := by
  intro h b
  exact DeltaSafe_of_fast (h b)

theorem OBL_INIT : BI_PAIR dataI 0 := by
  decide

theorem all_fault_sites_length : C_NZ_D3_sites.length = 68 := by
  decide

set_option maxHeartbeats 200000 in
theorem OBL_STEP_G0 : ∀ site ∈ faultSitesOf G0, SiteSafe site := by
  intro site h
  simp [G0, zGadget, faultSitesOf, deterministicSuffix] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b
    · exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
    · exact DeltaSafe_witness _ 0 1 (by decide) (by decide)
    · exact DeltaSafe_witness _ 0 1 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b
    · exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
    · exact DeltaSafe_witness _ 0 1 (by decide) (by decide)
    · exact DeltaSafe_witness _ 0 1 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)

set_option maxHeartbeats 200000 in
theorem OBL_STEP_G1 : ∀ site ∈ faultSitesOf G1, SiteSafe site := by
  intro site h
  simp [G1, xGadget, faultSitesOf, deterministicSuffix] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b
    · exact DeltaSafe_witness _ 2 0 (by decide) (by decide)
    · exact DeltaSafe_witness _ 2 0 (by decide) (by decide)
    · exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b
    · exact DeltaSafe_witness _ 2 0 (by decide) (by decide)
    · exact DeltaSafe_witness _ 2 0 (by decide) (by decide)
    · exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)

set_option maxHeartbeats 200000 in
theorem OBL_STEP_G2 : ∀ site ∈ faultSitesOf G2, SiteSafe site := by
  intro site h
  simp [G2, xGadget, faultSitesOf, deterministicSuffix] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b
    · exact DeltaSafe_witness _ 4 0 (by decide) (by decide)
    · exact DeltaSafe_witness _ 4 0 (by decide) (by decide)
    · exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b
    · exact DeltaSafe_witness _ 4 0 (by decide) (by decide)
    · exact DeltaSafe_witness _ 4 0 (by decide) (by decide)
    · exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)

set_option maxHeartbeats 200000 in
theorem OBL_STEP_G3 : ∀ site ∈ faultSitesOf G3, SiteSafe site := by
  intro site h
  simp [G3, zGadget, faultSitesOf, deterministicSuffix] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b
    · exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
    · exact DeltaSafe_witness _ 0 8 (by decide) (by decide)
    · exact DeltaSafe_witness _ 0 8 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b
    · exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
    · exact DeltaSafe_witness _ 0 8 (by decide) (by decide)
    · exact DeltaSafe_witness _ 0 8 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)
  · intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)

set_option maxHeartbeats 200000 in
theorem OBL_STEP_G4 : ∀ site ∈ faultSitesOf G4, SiteSafe site := by
  intro site h
  simp [G4, xGadget, faultSitesOf, deterministicSuffix] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)

set_option maxHeartbeats 200000 in
theorem OBL_STEP_G5 : ∀ site ∈ faultSitesOf G5, SiteSafe site := by
  intro site h
  simp [G5, zGadget, faultSitesOf, deterministicSuffix] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)

set_option maxHeartbeats 200000 in
theorem OBL_STEP_G6 : ∀ site ∈ faultSitesOf G6, SiteSafe site := by
  intro site h
  simp [G6, zGadget, faultSitesOf, deterministicSuffix] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)

set_option maxHeartbeats 200000 in
theorem OBL_STEP_G7 : ∀ site ∈ faultSitesOf G7, SiteSafe site := by
  intro site h
  simp [G7, xGadget, faultSitesOf, deterministicSuffix] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro b
    cases b <;> exact DeltaSafe_witness _ 0 0 (by decide) (by decide)

theorem OBL_STEP : ∀ site ∈ C_NZ_D3_sites, SiteSafe site := by
  intro site h
  simp [C_NZ_D3_sites] at h
  rcases h with h | h | h | h | h | h | h | h
  · exact OBL_STEP_G0 site h
  · exact OBL_STEP_G1 site h
  · exact OBL_STEP_G2 site h
  · exact OBL_STEP_G3 site h
  · exact OBL_STEP_G4 site h
  · exact OBL_STEP_G5 site h
  · exact OBL_STEP_G6 site h
  · exact OBL_STEP_G7 site h

theorem rowHasXb_nf_logicalX (m k : StabMask) (lz : Bool) (r : RowCol) :
    rowHasXb (pmul (prodStab k) (centralizerNFOf m true lz)) r = true := by
  fin_cases r
  · by_cases hm1 : m 1 <;> by_cases hm4 : m 4 <;>
      by_cases hk1 : k 1 <;> by_cases hk4 : k 4 <;>
      simp [rowHasXb, pmul, prodStab, centralizerNFOf, stabXBit, hasX_bitPauli_mul,
        hasX_logicalX, hm1, hm4, hk1, hk4]
  · by_cases hm1 : m 1 <;> by_cases hm2 : m 2 <;>
      by_cases hk1 : k 1 <;> by_cases hk2 : k 2 <;>
      simp [rowHasXb, pmul, prodStab, centralizerNFOf, stabXBit, hasX_bitPauli_mul,
        hasX_logicalX, hm1, hm2, hk1, hk2]
  · by_cases hm2 : m 2 <;> by_cases hm7 : m 7 <;>
      by_cases hk2 : k 2 <;> by_cases hk7 : k 7 <;>
      simp [rowHasXb, pmul, prodStab, centralizerNFOf, stabXBit, hasX_bitPauli_mul,
        hasX_logicalX, hm2, hm7, hk2, hk7]

theorem rowSpread_nf_logicalX :
    ∀ (m k : StabMask) (lz : Bool),
      rowSpreadX (pmul (prodStab k) (centralizerNFOf m true lz)) = 3 := by
  intro m k lz
  unfold rowSpreadX bcount3
  simp [rowHasXb_nf_logicalX]

theorem colHasZb_nf_logicalZ (m k : StabMask) (lx : Bool) (c : RowCol) :
    colHasZb (pmul (prodStab k) (centralizerNFOf m lx true)) c = true := by
  fin_cases c
  · by_cases hm0 : m 0 <;> by_cases hm6 : m 6 <;>
      by_cases hk0 : k 0 <;> by_cases hk6 : k 6 <;>
      simp [colHasZb, pmul, prodStab, centralizerNFOf, stabZBit, hasZ_bitPauli_mul,
        hasZ_logicalZ, hm0, hm6, hk0, hk6]
  · by_cases hm0 : m 0 <;> by_cases hm3 : m 3 <;>
      by_cases hk0 : k 0 <;> by_cases hk3 : k 3 <;>
      simp [colHasZb, pmul, prodStab, centralizerNFOf, stabZBit, hasZ_bitPauli_mul,
        hasZ_logicalZ, hm0, hm3, hk0, hk3]
  · by_cases hm3 : m 3 <;> by_cases hm5 : m 5 <;>
      by_cases hk3 : k 3 <;> by_cases hk5 : k 5 <;>
      simp [colHasZb, pmul, prodStab, centralizerNFOf, stabZBit, hasZ_bitPauli_mul,
        hasZ_logicalZ, hm3, hm5, hk3, hk5]

theorem colSpread_nf_logicalZ :
    ∀ (m k : StabMask) (lx : Bool),
      colSpreadZ (pmul (prodStab k) (centralizerNFOf m lx true)) = 3 := by
  intro m k lx
  unfold colSpreadZ bcount3
  simp [colHasZb_nf_logicalZ]

theorem not_XRowsLe_of_rowSpread3 {E : DataPauli} {f : Nat}
    (hrow : ∀ k : StabMask, rowSpreadX (pmul (prodStab k) E) = 3)
    (hf : f < 3) : ¬ XRowsLe E f := by
  intro hX
  unfold XRowsLe at hX
  rcases Finset.card_pos.mp hX with ⟨k, hk⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  rw [hrow k] at hk
  omega

theorem not_ZColsLe_of_colSpread3 {E : DataPauli} {f : Nat}
    (hcol : ∀ k : StabMask, colSpreadZ (pmul (prodStab k) E) = 3)
    (hf : f < 3) : ¬ ZColsLe E f := by
  intro hZ
  unfold ZColsLe at hZ
  rcases Finset.card_pos.mp hZ with ⟨k, hk⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  rw [hcol k] at hk
  omega

theorem OBL_DIST_NF_X :
    ∀ (m : StabMask) (f : Fin 3), ¬ BI_PAIR (centralizerNFOf m true false) f.val := by
  intro m f hBI
  exact (not_XRowsLe_of_rowSpread3 (fun k => rowSpread_nf_logicalX m k false) f.isLt) hBI.1

theorem OBL_DIST_NF_Z :
    ∀ (m : StabMask) (f : Fin 3), ¬ BI_PAIR (centralizerNFOf m false true) f.val := by
  intro m f hBI
  exact (not_ZColsLe_of_colSpread3 (fun k => colSpread_nf_logicalZ m k false) f.isLt) hBI.2

theorem OBL_DIST_NF_XZ :
    ∀ (m : StabMask) (f : Fin 3), ¬ BI_PAIR (centralizerNFOf m true true) f.val := by
  intro m f hBI
  exact (not_XRowsLe_of_rowSpread3 (fun k => rowSpread_nf_logicalX m k true) f.isLt) hBI.1

theorem OBL_DIST_NF (m : StabMask) (lx lz : Bool)
    (hlog : lx = true ∨ lz = true) (f : Fin 3) :
    ¬ BI_PAIR (centralizerNFOf m lx lz) f.val := by
  cases lx <;> cases lz <;> simp at hlog
  · exact OBL_DIST_NF_Z m f
  · exact OBL_DIST_NF_X m f
  · exact OBL_DIST_NF_XZ m f

theorem OBL_DIST_lt3 :
    ∀ E : DataPauli, LogicalAny E -> ∀ f : Fin 3, ¬ BI_PAIR E f.val := by
  intro E hLog f hBI
  rcases hLog with ⟨hCent, hNotStab⟩
  have hNF := centralizer_normal_form E hCent
  have hlogbits : logicalXBit E = true ∨ logicalZBit E = true := by
    by_cases hx : logicalXBit E = true
    · exact Or.inl hx
    · by_cases hz : logicalZBit E = true
      · exact Or.inr hz
      · exfalso
        apply hNotStab
        unfold Stab
        apply Finset.card_pos.mpr
        refine ⟨centralizerMask E, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hxFalse : logicalXBit E = false := bool_false_of_not_true hx
        have hzFalse : logicalZBit E = false := bool_false_of_not_true hz
        calc
          E = centralizerNF E := hNF
          _ = prodStab (centralizerMask E) := by
            simp [centralizerNF, hxFalse, hzFalse, centralizerNFOf_stab]
  rw [hNF] at hBI
  exact (OBL_DIST_NF (centralizerMask E) (logicalXBit E) (logicalZBit E) hlogbits f) hBI

theorem logicalX_real : LogicalAny logicalX := by
  decide

theorem logicalZ_real : LogicalAny logicalZ := by
  decide

theorem BI_PAIR_not_trivial : ¬ BI_PAIR logicalX 2 := by
  decide

theorem FORMULA_AGREEMENT_XRowsLe (E : DataPauli) (f : Nat) :
    XRowsLe E f ↔
      ((Finset.univ.filter fun m : StabMask => rowSpreadX (pmul (prodStab m) E) ≤ f).card > 0) :=
  Iff.rfl

theorem FORMULA_AGREEMENT_ZColsLe (E : DataPauli) (f : Nat) :
    ZColsLe E f ↔
      ((Finset.univ.filter fun m : StabMask => colSpreadZ (pmul (prodStab m) E) ≤ f).card > 0) :=
  Iff.rfl

inductive RunSites : List FaultSite -> DataPauli -> Nat -> DataPauli -> Nat -> Prop where
  | nil (E : DataPauli) (f : Nat) : RunSites [] E f E f
  | noFault {site sites E f E' f'} :
      RunSites sites E f E' f' ->
      RunSites (site :: sites) E f E' f'
  | fault {site sites E f E' f'} (b : FaultBranch) :
      RunSites sites (pmul E (faultDelta site b)) (f + 1) E' f' ->
      RunSites (site :: sites) E f E' f'

def CircuitRun (E : DataPauli) (f : Nat) : Prop :=
  RunSites C_NZ_D3_sites dataI 0 E f

def surfaceD3_distance_bound : Nat := 3

def runScript : List FaultSite -> List (Option FaultBranch) -> DataPauli -> Nat ->
    DataPauli × Nat
  | [], _, E, f => (E, f)
  | _ :: sites, [], E, f => runScript sites [] E f
  | _ :: sites, none :: script, E, f => runScript sites script E f
  | site :: sites, some b :: script, E, f =>
      runScript sites script (pmul E (faultDelta site b)) (f + 1)

theorem runScript_sound :
    ∀ (sites : List FaultSite) (script : List (Option FaultBranch)) (E : DataPauli)
      (f : Nat),
      RunSites sites E f (runScript sites script E f).1 (runScript sites script E f).2 := by
  intro sites
  induction sites with
  | nil =>
      intro script E f
      simp [runScript, RunSites.nil]
  | cons site sites ih =>
      intro script E f
      cases script with
      | nil =>
          exact RunSites.noFault (ih [] E f)
      | cons step script =>
          cases step with
          | none =>
              exact RunSites.noFault (ih script E f)
          | some b =>
              exact RunSites.fault b (ih script (pmul E (faultDelta site b)) (f + 1))

def reachLogicalXScript : List (Option FaultBranch) :=
  (List.range C_NZ_D3_sites.length).map fun i =>
    if i = 1 ∨ i = 3 ∨ i = 27 then some FaultBranch.X else none

theorem reachLogicalXScript_eval :
    runScript C_NZ_D3_sites reachLogicalXScript dataI 0 = (logicalX, 3) := by
  decide

theorem circuitRun_logicalX_three_faults : CircuitRun logicalX 3 := by
  have hrun := runScript_sound C_NZ_D3_sites reachLogicalXScript dataI 0
  simpa [CircuitRun, reachLogicalXScript_eval] using hrun

theorem surfaceD3_distance_reachable :
    ∃ E : DataPauli, CircuitRun E surfaceD3_distance_bound ∧ LogicalAny E := by
  exact ⟨logicalX, by simpa [surfaceD3_distance_bound] using circuitRun_logicalX_three_faults,
    logicalX_real⟩

theorem runSites_preserves_BI_PAIR {sites : List FaultSite} {E f E' f' : _} :
    (∀ site ∈ sites, SiteSafe site) ->
    RunSites sites E f E' f' ->
    BI_PAIR E f ->
    BI_PAIR E' f' := by
  intro hsafe hrun hBI
  induction hrun with
  | nil => exact hBI
  | noFault htail ih =>
      exact ih (fun site hmem => hsafe site (List.mem_cons_of_mem _ hmem)) hBI
  | fault b htail ih =>
      have hsite : SiteSafe _ := hsafe _ List.mem_cons_self
      have htailSafe : ∀ site ∈ _, SiteSafe site :=
        fun site hmem => hsafe site (List.mem_cons_of_mem _ hmem)
      exact ih htailSafe (BI_PAIR_pmul_of_delta_safe hBI (hsite b))

theorem invariant_of_circuit_run {E : DataPauli} {f : Nat} :
    CircuitRun E f -> BI_PAIR E f := by
  intro hrun
  exact runSites_preserves_BI_PAIR OBL_STEP hrun OBL_INIT

theorem data_distance_from_BI_PAIR {E : DataPauli} {f : Nat} :
    BI_PAIR E f -> LogicalAny E -> 3 ≤ f := by
  intro hBI hLog
  by_contra hnot
  have hlt : f < 3 := Nat.lt_of_not_ge hnot
  exact (OBL_DIST_lt3 E hLog ⟨f, hlt⟩) hBI

/-- Stronger detection-free circuit-distance lower bound for the concrete
surface-d3 NZ QClifford single-location Pauli fault model. -/
theorem surfaceD3_circuit_distance_lower_bound {E : DataPauli} {faults : Nat} :
    CircuitRun E faults -> LogicalAny E -> surfaceD3_distance_bound ≤ faults := by
  intro hrun hlog
  simpa [surfaceD3_distance_bound] using
    data_distance_from_BI_PAIR (invariant_of_circuit_run hrun) hlog

/-- Certificate-shaped wrapper.  `ZeroDet` is vestigial for this lower bound. -/
theorem surfaceD3_DIST_CIRC_D3 {det : DetVec} {E : DataPauli} {faults : Nat} :
    CircuitRun E faults ->
      (ZeroDet det ∧ LogicalAny E -> surfaceD3_distance_bound ≤ faults) := by
  intro hrun h
  exact surfaceD3_circuit_distance_lower_bound hrun h.2

theorem surfaceD3_circuit_distance_exact :
    (∀ {E : DataPauli} {faults : Nat},
        CircuitRun E faults -> LogicalAny E -> surfaceD3_distance_bound ≤ faults) ∧
      (∃ E : DataPauli, CircuitRun E surfaceD3_distance_bound ∧ LogicalAny E) := by
  constructor
  · intro E faults hrun hlog
    exact surfaceD3_circuit_distance_lower_bound hrun hlog
  · exact surfaceD3_distance_reachable

def Assertion := PhysPauli -> Nat -> Prop

def wpGate (g : GateOp) (Q : Assertion) : Assertion :=
  fun phys faults => Q (mapGate g phys) faults

def frontier (suffix : List GateOp) : Assertion :=
  fun phys faults => BI_PAIR (dataOf (PropDet suffix phys)) faults

def cleanPre : Assertion :=
  fun phys faults => phys = physI ∧ faults = 0

def distPost : Assertion :=
  fun phys faults => LogicalAny (dataOf phys) -> surfaceD3_distance_bound ≤ faults

def FaultFrontierSide (q : PhysQ) (suffix : List GateOp) : Prop :=
  SiteSafe { q := q, suffix := suffix }

inductive HDeriv : Assertion -> List IOp -> Assertion -> Type where
  | hNil {P : Assertion} : HDeriv P [] P
  | hSeq {P Q R : Assertion} {a b : List IOp} :
      HDeriv P a Q -> HDeriv Q b R -> HDeriv P (a ++ b) R
  | hConseq {P P' Q Q' : Assertion} {c : List IOp} :
      (∀ phys faults, P phys faults -> P' phys faults) ->
      HDeriv P' c Q' ->
      (∀ phys faults, Q' phys faults -> Q phys faults) ->
      HDeriv P c Q
  | hGate (g : GateOp) (Q : Assertion) : HDeriv (wpGate g Q) [.gate g] Q
  | hFault (q : PhysQ) (suffix : List GateOp) :
      FaultFrontierSide q suffix -> HDeriv (frontier suffix) [.fault q] (frontier suffix)

theorem Exec_append_inv {a b : List IOp} {phys faults phys' faults'} :
    Exec (a ++ b) phys faults phys' faults' ->
      ∃ mid midFaults,
        Exec a phys faults mid midFaults ∧ Exec b mid midFaults phys' faults' := by
  induction a generalizing phys faults with
  | nil =>
      intro h
      exact ⟨phys, faults, Exec.nil phys faults, h⟩
  | cons op rest ih =>
      intro h
      cases op with
      | gate g =>
          cases h with
          | gate htail =>
              rcases ih htail with ⟨mid, midFaults, hrest, hb⟩
              exact ⟨mid, midFaults, Exec.gate hrest, hb⟩
      | fault q =>
          cases h with
          | faultNone htail =>
              rcases ih htail with ⟨mid, midFaults, hrest, hb⟩
              exact ⟨mid, midFaults, Exec.faultNone hrest, hb⟩
          | faultSome b htail =>
              rcases ih htail with ⟨mid, midFaults, hrest, hb⟩
              exact ⟨mid, midFaults, Exec.faultSome b hrest, hb⟩

theorem frontier_fault_preserved {q : PhysQ} {suffix : List GateOp} {b : FaultBranch}
    {phys : PhysPauli} {faults : Nat} :
    FaultFrontierSide q suffix ->
    frontier suffix phys faults ->
    frontier suffix (phMul phys (singlePhys q b.toPauli)) (faults + 1) := by
  intro hSide hFrontier
  unfold FaultFrontierSide SiteSafe at hSide
  unfold frontier at hFrontier ⊢
  rw [PropDet_phMul, dataOf_phMul]
  exact BI_PAIR_pmul_of_delta_safe hFrontier (hSide b)

theorem hoareSound {P Q : Assertion} {c : List IOp} (d : HDeriv P c Q) :
    ∀ {phys faults phys' faults'},
      Exec c phys faults phys' faults' -> P phys faults -> Q phys' faults' := by
  induction d with
  | hNil =>
      intro phys faults phys' faults' hExec hP
      cases hExec
      exact hP
  | hSeq da db iha ihb =>
      intro phys faults phys' faults' hExec hP
      rcases Exec_append_inv hExec with ⟨mid, midFaults, hA, hB⟩
      exact ihb hB (iha hA hP)
  | hConseq hPre d hPost ih =>
      intro phys faults phys' faults' hExec hP
      exact hPost phys' faults' (ih hExec (hPre phys faults hP))
  | hGate g Q =>
      intro phys faults phys' faults' hExec hP
      cases hExec with
      | gate htail =>
          cases htail
          exact hP
  | hFault q suffix hSide =>
      intro phys faults phys' faults' hExec hP
      cases hExec with
      | faultNone htail =>
          cases htail
          exact hP
      | faultSome b htail =>
          cases htail
          exact frontier_fault_preserved hSide hP

def instrFrontierDeriv (op : IOp) (rest : List IOp)
    (hSafe : ∀ site ∈ faultSitesOf (op :: rest), SiteSafe site) :
    HDeriv (frontier (deterministicSuffix (op :: rest))) [op]
      (frontier (deterministicSuffix rest)) := by
  cases op with
  | gate g =>
      exact HDeriv.hGate g (frontier (deterministicSuffix rest))
  | fault q =>
      exact HDeriv.hFault q (deterministicSuffix rest)
        (hSafe { q := q, suffix := deterministicSuffix rest } (by simp [faultSitesOf]))

def tailSiteSafe {op : IOp} {rest : List IOp}
    (hSafe : ∀ site ∈ faultSitesOf (op :: rest), SiteSafe site) :
    ∀ site ∈ faultSitesOf rest, SiteSafe site := by
  intro site hmem
  cases op <;> exact hSafe site (by simp [faultSitesOf, hmem])

def frontierDeriv :
    (ops : List IOp) ->
      (∀ site ∈ faultSitesOf ops, SiteSafe site) ->
      HDeriv (frontier (deterministicSuffix ops)) ops (frontier [])
  | [], _ => HDeriv.hNil
  | op :: rest, hSafe =>
      HDeriv.hSeq (instrFrontierDeriv op rest hSafe)
        (frontierDeriv rest (tailSiteSafe hSafe))

theorem dataOf_det_G0 (phys : PhysPauli) :
    dataOf (PropDet (deterministicSuffix G0) phys) = dataOf phys := by
  simpa [G0] using dataOf_det_zGadget [pq 0, pq 3, pq 1, pq 4] phys (by decide)

theorem dataOf_det_G1 (phys : PhysPauli) :
    dataOf (PropDet (deterministicSuffix G1) phys) = dataOf phys := by
  simpa [G1] using dataOf_det_xGadget [pq 1, pq 2, pq 4, pq 5] phys (by decide)

theorem dataOf_det_G2 (phys : PhysPauli) :
    dataOf (PropDet (deterministicSuffix G2) phys) = dataOf phys := by
  simpa [G2] using dataOf_det_xGadget [pq 3, pq 4, pq 6, pq 7] phys (by decide)

theorem dataOf_det_G3 (phys : PhysPauli) :
    dataOf (PropDet (deterministicSuffix G3) phys) = dataOf phys := by
  simpa [G3] using dataOf_det_zGadget [pq 4, pq 7, pq 5, pq 8] phys (by decide)

theorem dataOf_det_G4 (phys : PhysPauli) :
    dataOf (PropDet (deterministicSuffix G4) phys) = dataOf phys := by
  simpa [G4] using dataOf_det_xGadget [pq 0, pq 1] phys (by decide)

theorem dataOf_det_G5 (phys : PhysPauli) :
    dataOf (PropDet (deterministicSuffix G5) phys) = dataOf phys := by
  simpa [G5] using dataOf_det_zGadget [pq 2, pq 5] phys (by decide)

theorem dataOf_det_G6 (phys : PhysPauli) :
    dataOf (PropDet (deterministicSuffix G6) phys) = dataOf phys := by
  simpa [G6] using dataOf_det_zGadget [pq 3, pq 6] phys (by decide)

theorem dataOf_det_G7 (phys : PhysPauli) :
    dataOf (PropDet (deterministicSuffix G7) phys) = dataOf phys := by
  simpa [G7] using dataOf_det_xGadget [pq 7, pq 8] phys (by decide)

def gadgetBoundaryEntail (ops : List IOp)
    (hData : ∀ phys : PhysPauli,
      dataOf (PropDet (deterministicSuffix ops) phys) = dataOf phys) :
    ∀ phys faults, frontier [] phys faults -> frontier (deterministicSuffix ops) phys faults := by
  intro phys faults h
  unfold frontier at h ⊢
  simpa [hData phys] using h

def gadgetDeriv (ops : List IOp)
    (hSafe : ∀ site ∈ faultSitesOf ops, SiteSafe site)
    (hData : ∀ phys : PhysPauli,
      dataOf (PropDet (deterministicSuffix ops) phys) = dataOf phys) :
    HDeriv (frontier []) ops (frontier []) :=
  HDeriv.hConseq (gadgetBoundaryEntail ops hData) (frontierDeriv ops hSafe)
    (fun _ _ h => h)

def hoareG0Deriv : HDeriv (frontier []) G0 (frontier []) :=
  gadgetDeriv G0 OBL_STEP_G0 dataOf_det_G0

def hoareG1Deriv : HDeriv (frontier []) G1 (frontier []) :=
  gadgetDeriv G1 OBL_STEP_G1 dataOf_det_G1

def hoareG2Deriv : HDeriv (frontier []) G2 (frontier []) :=
  gadgetDeriv G2 OBL_STEP_G2 dataOf_det_G2

def hoareG3Deriv : HDeriv (frontier []) G3 (frontier []) :=
  gadgetDeriv G3 OBL_STEP_G3 dataOf_det_G3

def hoareG4Deriv : HDeriv (frontier []) G4 (frontier []) :=
  gadgetDeriv G4 OBL_STEP_G4 dataOf_det_G4

def hoareG5Deriv : HDeriv (frontier []) G5 (frontier []) :=
  gadgetDeriv G5 OBL_STEP_G5 dataOf_det_G5

def hoareG6Deriv : HDeriv (frontier []) G6 (frontier []) :=
  gadgetDeriv G6 OBL_STEP_G6 dataOf_det_G6

def hoareG7Deriv : HDeriv (frontier []) G7 (frontier []) :=
  gadgetDeriv G7 OBL_STEP_G7 dataOf_det_G7

def hoareCoreDeriv : HDeriv (frontier []) C_NZ_D3_prog (frontier []) :=
  HDeriv.hSeq hoareG0Deriv <|
    HDeriv.hSeq hoareG1Deriv <|
      HDeriv.hSeq hoareG2Deriv <|
        HDeriv.hSeq hoareG3Deriv <|
          HDeriv.hSeq hoareG4Deriv <|
            HDeriv.hSeq hoareG5Deriv <|
              HDeriv.hSeq hoareG6Deriv hoareG7Deriv

theorem cleanPre_to_frontier :
    ∀ phys faults, cleanPre phys faults -> frontier [] phys faults := by
  intro phys faults h
  rcases h with ⟨rfl, rfl⟩
  unfold frontier
  exact OBL_INIT

theorem finalGeo_entail :
    ∀ phys faults, frontier [] phys faults -> distPost phys faults := by
  intro phys faults hFrontier hLogical
  unfold frontier at hFrontier
  simpa [distPost, PropDet, surfaceD3_distance_bound] using
    data_distance_from_BI_PAIR hFrontier hLogical

def hoareDistDeriv : HDeriv cleanPre C_NZ_D3_prog distPost :=
  HDeriv.hConseq cleanPre_to_frontier
    (HDeriv.hConseq (fun _ _ h => h) hoareCoreDeriv finalGeo_entail)
    (fun _ _ h => h)

theorem surfaceD3_distance_via_hoare :
    ∀ phys faults phys' faults',
      Exec C_NZ_D3_prog phys faults phys' faults' -> cleanPre phys faults -> distPost phys' faults' := by
  intro phys faults phys' faults' hExec hClean
  exact hoareSound hoareDistDeriv hExec hClean

theorem surfaceD3_lower_bound_via_hoare {phys : PhysPauli} {faults : Nat} :
    Exec C_NZ_D3_prog physI 0 phys faults ->
    LogicalAny (dataOf phys) ->
    surfaceD3_distance_bound ≤ faults := by
  intro hExec hLogical
  exact surfaceD3_distance_via_hoare physI 0 phys faults hExec ⟨rfl, rfl⟩ hLogical

theorem surfaceD3_DIST_CIRC_D3_via_hoare {det : DetVec} {phys : PhysPauli}
    {faults : Nat} :
    Exec C_NZ_D3_prog physI 0 phys faults ->
    (ZeroDet det ∧ LogicalAny (dataOf phys) -> surfaceD3_distance_bound ≤ faults) := by
  intro hExec h
  exact surfaceD3_lower_bound_via_hoare hExec h.2

def execScript : List IOp -> List (Option FaultBranch) -> PhysPauli -> Nat -> PhysPauli × Nat
  | [], _, phys, faults => (phys, faults)
  | .gate g :: rest, script, phys, faults => execScript rest script (mapGate g phys) faults
  | .fault _ :: rest, [], phys, faults => execScript rest [] phys faults
  | .fault _ :: rest, none :: script, phys, faults => execScript rest script phys faults
  | .fault q :: rest, some b :: script, phys, faults =>
      execScript rest script (phMul phys (singlePhys q b.toPauli)) (faults + 1)

theorem execScript_sound :
    ∀ (ops : List IOp) (script : List (Option FaultBranch)) (phys : PhysPauli)
      (faults : Nat),
      Exec ops phys faults (execScript ops script phys faults).1
        (execScript ops script phys faults).2 := by
  intro ops
  induction ops with
  | nil =>
      intro script phys faults
      simp [execScript, Exec.nil]
  | cons op rest ih =>
      intro script phys faults
      cases op with
      | gate g =>
          exact Exec.gate (ih script (mapGate g phys) faults)
      | fault q =>
          cases script with
          | nil =>
              exact Exec.faultNone (ih [] phys faults)
          | cons step script =>
              cases step with
              | none =>
                  exact Exec.faultNone (ih script phys faults)
              | some b =>
                  exact Exec.faultSome b (ih script (phMul phys (singlePhys q b.toPauli))
                    (faults + 1))

theorem execScript_reachLogicalX_data :
    dataOf (execScript C_NZ_D3_prog reachLogicalXScript physI 0).1 = logicalX := by
  decide

theorem execScript_reachLogicalX_faults :
    (execScript C_NZ_D3_prog reachLogicalXScript physI 0).2 = 3 := by
  decide

theorem circuitRun_logicalX_three_faults_exec :
    ∃ phys : PhysPauli, Exec C_NZ_D3_prog physI 0 phys 3 ∧ LogicalAny (dataOf phys) := by
  let result := execScript C_NZ_D3_prog reachLogicalXScript physI 0
  have hExec := execScript_sound C_NZ_D3_prog reachLogicalXScript physI 0
  refine ⟨result.1, ?_, ?_⟩
  · simpa [result, execScript_reachLogicalX_faults] using hExec
  · rw [show dataOf result.1 = logicalX by
        simpa [result] using execScript_reachLogicalX_data]
    exact logicalX_real

def jsonJoin (xs : List String) : String :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: xs => x ++ "," ++ jsonJoin xs

def jsonQuote (s : String) : String :=
  "\"" ++ s ++ "\""

def jsonArray (xs : List String) : String :=
  "[" ++ jsonJoin xs ++ "]"

def jsonObject (fields : List (String × String)) : String :=
  "{" ++ jsonJoin (fields.map fun field => jsonQuote field.1 ++ ":" ++ field.2) ++ "}"

def pauliJsonName? : Pauli -> Option String
  | .I => none
  | .X => some "X"
  | .Y => some "Y"
  | .Z => some "Z"

def pauliSupportJson (E : DataPauli) : String :=
  jsonArray <| (List.finRange 9).filterMap fun q =>
    (pauliJsonName? (E q)).map fun p => jsonArray [toString q.val, jsonQuote p]

def namedDataPauliJson (name : String) (E : DataPauli) : String :=
  jsonObject [("name", jsonQuote name), ("support", pauliSupportJson E)]

def leanStabilizersJson : String :=
  jsonArray <| (List.finRange 8).map fun i => namedDataPauliJson ("s" ++ toString i.val) (stabAt i)

def leanLogicalsJson : String :=
  jsonObject [
    ("LX", pauliSupportJson logicalX),
    ("LZ", pauliSupportJson logicalZ)
  ]

def decodeZGadgetBody? : List IOp -> Option (List PhysQ)
  | [.fault a, .gate (.measZ b)] =>
      if a = pq 9 ∧ b = pq 9 then some [] else none
  | .fault q :: .fault a :: .gate (.cx c t) :: rest =>
      if a = pq 9 ∧ c = q ∧ t = pq 9 then
        (decodeZGadgetBody? rest).map fun order => q :: order
      else
        none
  | _ => none

def decodeZGadget? : List IOp -> Option (List PhysQ)
  | .fault a :: .gate (.prep0 b) :: rest =>
      if a = pq 9 ∧ b = pq 9 then decodeZGadgetBody? rest else none
  | _ => none

def decodeXGadgetBody? : List IOp -> Option (List PhysQ)
  | [.fault a, .gate (.h h), .fault b, .gate (.measZ m)] =>
      if a = pq 9 ∧ h = pq 9 ∧ b = pq 9 ∧ m = pq 9 then some [] else none
  | .fault a :: .fault q :: .gate (.cx c t) :: rest =>
      if a = pq 9 ∧ c = pq 9 ∧ t = q then
        (decodeXGadgetBody? rest).map fun order => q :: order
      else
        none
  | _ => none

def decodeXGadget? : List IOp -> Option (List PhysQ)
  | .fault a :: .gate (.prepP b) :: rest =>
      if a = pq 9 ∧ b = pq 9 then decodeXGadgetBody? rest else none
  | _ => none

def physOrderJson (order : List PhysQ) : String :=
  jsonArray <| order.map fun q => toString q.val

def leanGadgetJson (id : String) (ops : List IOp) : String :=
  match decodeZGadget? ops with
  | some order =>
      jsonObject [("id", jsonQuote id), ("kind", jsonQuote "MeasZStab"),
        ("order", physOrderJson order)]
  | none =>
      match decodeXGadget? ops with
      | some order =>
          jsonObject [("id", jsonQuote id), ("kind", jsonQuote "MeasXStab"),
            ("order", physOrderJson order)]
      | none =>
          jsonObject [("id", jsonQuote id), ("kind", jsonQuote "UNRECOGNIZED"),
            ("order", jsonArray [])]

def leanGadgetsJson : String :=
  jsonArray [
    leanGadgetJson "G0" G0,
    leanGadgetJson "G1" G1,
    leanGadgetJson "G2" G2,
    leanGadgetJson "G3" G3,
    leanGadgetJson "G4" G4,
    leanGadgetJson "G5" G5,
    leanGadgetJson "G6" G6,
    leanGadgetJson "G7" G7
  ]

def leanCertificateCorrespondenceJson : String :=
  jsonObject [
    ("stabilizers", leanStabilizersJson),
    ("logicals", leanLogicalsJson),
    ("gadgets", leanGadgetsJson),
    ("distance", toString surfaceD3_distance_bound)
  ]

#eval IO.println ("LEAN_CERT_CORRESPONDENCE_JSON:" ++ leanCertificateCorrespondenceJson)

#print axioms surfaceD3_circuit_distance_lower_bound
#print axioms surfaceD3_distance_reachable
#print axioms surfaceD3_circuit_distance_exact
#print HDeriv
#print axioms surfaceD3_distance_via_hoare

end QStab.Paper.SurfaceD3CircuitDistance
