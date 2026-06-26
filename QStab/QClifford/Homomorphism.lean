import QStab.QClifford.FaultSemantics

/-! # Clifford propagation is a Pauli homomorphism, and injection factors

The linchpin of the mechanical abstract-to-concrete translation: QClifford
propagation `propagateGate`/`propagateCircuit` is a homomorphism of the
phase-free Pauli group under the pointwise product `ErrorState.mul`. As a
corollary, injecting a single-qubit Pauli before a circuit **factors**:

  `propagateCircuit c (es.inject q p)
      = (propagateCircuit c es) * (propagateCircuit c (singleFault q p))`

so the lone-fault residual is independent of the ambient state `es`. This
is what reduces the alignment obligation of `gate_level_tolerates` to a
finite, state-free, per-(location, Pauli) check.
-/

namespace QStab.QClifford

/-- Pointwise Pauli product on error states (phase-free); measurement
    flips combine by xor. -/
def ErrorState.mul {nq : Nat} (es fs : ErrorState nq) : ErrorState nq where
  paulis := fun i => pauliMul (es.paulis i) (fs.paulis i)
  measFlips := fun i => xor (es.measFlips i) (fs.measFlips i)

/-- Componentwise extensionality for error states. -/
theorem ErrorState.ext' {nq : Nat} {a b : ErrorState nq}
    (hp : a.paulis = b.paulis) (hm : a.measFlips = b.measFlips) : a = b := by
  cases a; cases b; cases hp; cases hm; rfl

/-! ## Per-Pauli homomorphisms (exhaustive checks) -/

theorem pauliMul_comm (a b : Pauli) : pauliMul a b = pauliMul b a := by
  cases a <;> cases b <;> rfl

theorem pauliMul_mid_swap (a b c d : Pauli) :
    pauliMul (pauliMul a b) (pauliMul c d) = pauliMul (pauliMul a c) (pauliMul b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem xPart_pauliMul (a b : Pauli) :
    xPart (pauliMul a b) = pauliMul (xPart a) (xPart b) := by
  cases a <;> cases b <;> rfl

theorem zPart_pauliMul (a b : Pauli) :
    zPart (pauliMul a b) = pauliMul (zPart a) (zPart b) := by
  cases a <;> cases b <;> rfl

theorem hadamardAction_pauliMul (a b : Pauli) :
    hadamardAction (pauliMul a b) = pauliMul (hadamardAction a) (hadamardAction b) := by
  cases a <;> cases b <;> rfl

theorem hasXComp_pauliMul (a b : Pauli) :
    hasXComp (pauliMul a b) = xor (hasXComp a) (hasXComp b) := by
  cases a <;> cases b <;> rfl

/-! ## Gate and circuit propagation are homomorphisms -/

theorem propagateGate_mul {nq : Nat} (g : Gate nq) (es fs : ErrorState nq) :
    propagateGate g (es.mul fs) = (propagateGate g es).mul (propagateGate g fs) := by
  apply ErrorState.ext'
  · funext i
    cases g with
    | cnot c t hne =>
        simp only [propagateGate, ErrorState.mul]
        split_ifs with h1 h2
        · rw [xPart_pauliMul]; exact pauliMul_mid_swap _ _ _ _
        · rw [zPart_pauliMul]; exact pauliMul_mid_swap _ _ _ _
        · rfl
    | hadamard q =>
        simp only [propagateGate, ErrorState.mul]
        split_ifs with h1
        · exact hadamardAction_pauliMul _ _
        · rfl
    | prepZero q =>
        simp only [propagateGate, ErrorState.mul]
        split_ifs with h1 <;> rfl
    | prepPlus q =>
        simp only [propagateGate, ErrorState.mul]
        split_ifs with h1 <;> rfl
    | measZ q =>
        simp only [propagateGate, ErrorState.mul]
  · funext i
    cases g with
    | cnot c t hne => simp only [propagateGate, ErrorState.mul]
    | hadamard q => simp only [propagateGate, ErrorState.mul]
    | prepZero q => simp only [propagateGate, ErrorState.mul]
    | prepPlus q => simp only [propagateGate, ErrorState.mul]
    | measZ q =>
        simp only [propagateGate, ErrorState.mul]
        split_ifs with h1
        · rw [hasXComp_pauliMul]
          generalize es.measFlips i = a
          generalize fs.measFlips i = b
          generalize hasXComp (es.paulis q) = u
          generalize hasXComp (fs.paulis q) = v
          revert a b u v; decide
        · rfl

theorem propagateCircuit_mul {nq : Nat} (c : Circuit nq) (es fs : ErrorState nq) :
    propagateCircuit c (es.mul fs) = (propagateCircuit c es).mul (propagateCircuit c fs) := by
  induction c generalizing es fs with
  | nil => rfl
  | cons g gs ih =>
      simp only [propagateCircuit]
      rw [propagateGate_mul, ih]

/-! ## Injection factors through propagation -/

/-- The state with a single Pauli `p` on qubit `q` over the clean state. -/
def singleFault {nq : Nat} (q : Fin nq) (p : Pauli) : ErrorState nq :=
  (ErrorState.clean nq).inject q p

/-- `es.inject q p = es * singleFault q p`: a single injection is right
    multiplication by the lone fault. -/
theorem inject_eq_mul {nq : Nat} (es : ErrorState nq) (q : Fin nq) (p : Pauli) :
    es.inject q p = es.mul (singleFault q p) := by
  apply ErrorState.ext'
  · funext i
    simp only [ErrorState.inject, ErrorState.mul, singleFault, ErrorState.clean]
    split_ifs with h
    · rw [pauliMul_I_right]; exact pauliMul_comm _ _
    · rw [pauliMul_I_right]
  · funext i
    simp [ErrorState.inject, ErrorState.mul, singleFault, ErrorState.clean]

/-- **Factorisation of an injection through a circuit.** The residual of
    `(state + lone fault)` is the residual of the state times the residual
    of the lone fault — and the latter is independent of the state. -/
theorem propagateCircuit_inject_factor {nq : Nat} (c : Circuit nq)
    (es : ErrorState nq) (q : Fin nq) (p : Pauli) :
    propagateCircuit c (es.inject q p) =
    (propagateCircuit c es).mul (propagateCircuit c (singleFault q p)) := by
  rw [inject_eq_mul, propagateCircuit_mul]

end QStab.QClifford
