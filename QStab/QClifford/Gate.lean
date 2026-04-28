import LeanQEC.Pauli

/-! # QClifford gate-level primitives

Defines Clifford gates, syndrome extraction circuits, and the
Pauli error propagation rules through each gate type.

The Heisenberg picture: we track how Pauli errors transform
through Clifford gates, without simulating quantum states.
-/

namespace QStab.QClifford

/-! ### Pauli multiplication (ignoring global phase) -/

/-- Pauli group multiplication table (phase-free).
    I·P = P, P·P = I, X·Y = Z, Y·Z = X, Z·X = Y (cyclic). -/
def pauliMul : Pauli → Pauli → Pauli
  | .I, p => p
  | p, .I => p
  | .X, .X => .I
  | .X, .Y => .Z
  | .X, .Z => .Y
  | .Y, .X => .Z
  | .Y, .Y => .I
  | .Y, .Z => .X
  | .Z, .X => .Y
  | .Z, .Y => .X
  | .Z, .Z => .I

/-! ### Clifford gates -/

/-- A Clifford gate on nq qubits. -/
inductive Gate (nq : Nat) where
  /-- CNOT: X propagates control→target, Z propagates target→control -/
  | cnot (control target : Fin nq) (hne : control ≠ target)
  /-- Hadamard: swaps X↔Z on one qubit -/
  | hadamard (q : Fin nq)
  /-- Prepare |0⟩: resets qubit to |0⟩ (removes any prior error on that qubit) -/
  | prepZero (q : Fin nq)
  /-- Prepare |+⟩: resets qubit to |+⟩ -/
  | prepPlus (q : Fin nq)
  /-- Measure in Z basis: Z error has no effect, X/Y error flips outcome -/
  | measZ (q : Fin nq)

/-- A circuit is a list of gates. -/
def Circuit (nq : Nat) := List (Gate nq)

/-! ### Pauli error propagation through gates (Heisenberg picture)

Key rules:
- CNOT(c,t): X_c → X_c·X_t, Z_t → Z_c·Z_t, X_t → X_t, Z_c → Z_c
  For Y = iXZ: Y_c → Y_c·X_t, Y_t → X_c·Y_t (from decomposition)
- H: X ↔ Z on that qubit (Y → -Y, but we ignore phase)
- PrepZero: any error on that qubit is removed (reset)
- PrepPlus: any error on that qubit is removed (reset)
- MeasZ: X/Y on measured qubit → measurement flips; Z → no flip
-/

/-- An error state: Pauli on each qubit + accumulated measurement flips. -/
structure ErrorState (nq : Nat) where
  paulis : Fin nq → Pauli
  measFlips : Fin nq → Bool  -- track measurement flips per qubit

/-- Initial error state: no errors, no flips. -/
def ErrorState.clean (nq : Nat) : ErrorState nq where
  paulis := fun _ => .I
  measFlips := fun _ => false

/-- Inject a single Pauli error on qubit q. -/
def ErrorState.inject (es : ErrorState nq) (q : Fin nq) (p : Pauli) : ErrorState nq where
  paulis := fun i => if i = q then pauliMul p (es.paulis i) else es.paulis i
  measFlips := es.measFlips

/-- Has X-component: X or Y. -/
def hasXComp : Pauli → Bool
  | .X => true
  | .Y => true
  | _ => false

/-- Has Z-component: Z or Y. -/
def hasZComp : Pauli → Bool
  | .Z => true
  | .Y => true
  | _ => false

/-- Extract the X-component of a Pauli (for CNOT propagation). -/
def xPart : Pauli → Pauli
  | .X => .X
  | .Y => .X
  | _ => .I

/-- Extract the Z-component of a Pauli (for CNOT propagation). -/
def zPart : Pauli → Pauli
  | .Z => .Z
  | .Y => .Z
  | _ => .I

/-- Hadamard action on a single Pauli: X↔Z, Y→Y, I→I. -/
def hadamardAction : Pauli → Pauli
  | .I => .I
  | .X => .Z
  | .Z => .X
  | .Y => .Y

/-- Propagate an error state through a single gate. -/
def propagateGate (g : Gate nq) (es : ErrorState nq) : ErrorState nq :=
  match g with
  | .cnot c t _ =>
    -- CNOT propagation:
    -- X on control → X on control ⊗ X on target
    -- Z on target → Z on control ⊗ Z on target
    -- Combined: if control has X-component, target gets X too
    --           if target has Z-component, control gets Z too
    let xFromControl := xPart (es.paulis c)   -- X part of control error
    let zFromTarget := zPart (es.paulis t)    -- Z part of target error
    { paulis := fun i =>
        if i = t then pauliMul xFromControl (es.paulis t)  -- target gets X from control
        else if i = c then pauliMul zFromTarget (es.paulis c)  -- control gets Z from target
        else es.paulis i
      measFlips := es.measFlips }
  | .hadamard q =>
    { paulis := fun i => if i = q then hadamardAction (es.paulis i) else es.paulis i
      measFlips := es.measFlips }
  | .prepZero q =>
    -- Reset removes error on q
    { paulis := fun i => if i = q then .I else es.paulis i
      measFlips := es.measFlips }
  | .prepPlus q =>
    -- Reset removes error on q
    { paulis := fun i => if i = q then .I else es.paulis i
      measFlips := es.measFlips }
  | .measZ q =>
    -- Z-basis measurement: X/Y on q flips the measurement outcome
    { paulis := es.paulis  -- error on measured qubit consumed by measurement
      measFlips := fun i => if i = q then xor (es.measFlips i) (hasXComp (es.paulis q))
                             else es.measFlips i }

/-- Propagate through a circuit (list of gates). -/
def propagateCircuit : Circuit nq → ErrorState nq → ErrorState nq
  | [], es => es
  | g :: gs, es => propagateCircuit gs (propagateGate g es)

/-! ### Fault injection and effect computation -/

/-- A fault: inject Pauli p on qubit q before gate at position pos. -/
structure Fault (nq : Nat) where
  position : Nat       -- inject before the gate at this index (0 = before first gate)
  qubit : Fin nq
  pauli : Pauli
  hp : pauli ≠ .I

/-- Split a circuit at position pos: gates before and gates after. -/
def splitAt (circuit : Circuit nq) (pos : Nat) : Circuit nq × Circuit nq :=
  (circuit.take pos, circuit.drop pos)

/-- Compute the effect of a single fault: run gates before the fault,
    inject the error, run gates after the fault. -/
def computeFaultEffect (circuit : Circuit nq) (fault : Fault nq) : ErrorState nq :=
  let (before, after) := splitAt circuit fault.position
  let es := propagateCircuit before (ErrorState.clean nq)
  let es' := es.inject fault.qubit fault.pauli
  propagateCircuit after es'

/-! ### Verification lemmas for Pauli propagation -/

@[simp] theorem pauliMul_I_left (p : Pauli) : pauliMul .I p = p := by cases p <;> rfl
@[simp] theorem pauliMul_I_right (p : Pauli) : pauliMul p .I = p := by cases p <;> rfl
@[simp] theorem pauliMul_self (p : Pauli) : pauliMul p p = .I := by cases p <;> rfl

@[simp] theorem hadamardAction_X : hadamardAction .X = .Z := rfl
@[simp] theorem hadamardAction_Z : hadamardAction .Z = .X := rfl
@[simp] theorem hadamardAction_Y : hadamardAction .Y = .Y := rfl
@[simp] theorem hadamardAction_I : hadamardAction .I = .I := rfl

@[simp] theorem hasXComp_X : hasXComp .X = true := rfl
@[simp] theorem hasXComp_Y : hasXComp .Y = true := rfl
@[simp] theorem hasXComp_Z : hasXComp .Z = false := rfl
@[simp] theorem hasXComp_I : hasXComp .I = false := rfl

@[simp] theorem xPart_X : xPart .X = .X := rfl
@[simp] theorem xPart_Y : xPart .Y = .X := rfl
@[simp] theorem xPart_Z : xPart .Z = .I := rfl
@[simp] theorem xPart_I : xPart .I = .I := rfl

@[simp] theorem zPart_Z : zPart .Z = .Z := rfl
@[simp] theorem zPart_Y : zPart .Y = .Z := rfl
@[simp] theorem zPart_X : zPart .X = .I := rfl
@[simp] theorem zPart_I : zPart .I = .I := rfl

end QStab.QClifford
