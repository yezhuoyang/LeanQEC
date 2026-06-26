import QStab.QClifford.Gate

/-! # CZ as a derived QClifford gadget

The mechanized gate kernel is `{CNOT, H, prepZero, prepPlus, measZ}`
(`QClifford.Gate`). To keep that kernel minimal we realise the
controlled-Z gate as the standard identity
`CZ(a,b) = H(b);\ CNOT(a,b);\ H(b)` (`czCircuit`) rather than as a new
`Gate` constructor — which would force a new case in every `match` on
`Gate` across the development. `czApply` is the closed-form propagation
rule of `fig:qcliff-rules` (each qubit gains a `Z` iff the other carries
an `X`-component); the `example`s below check that the gadget realises
that rule on representative inputs. -/

namespace QStab.QClifford

/-- `CZ(a,b)` realised as `H(b); CNOT(a,b); H(b)`. -/
def czCircuit {nq : Nat} (a b : Fin nq) (hne : a ≠ b) : Circuit nq :=
  [Gate.hadamard b, Gate.cnot a b hne, Gate.hadamard b]

/-- The CZ propagation rule of Figure~\ref{fig:qcliff-rules} in closed
    form: qubit `a` gains a `Z` iff `b` has an `X`-component, and
    symmetrically. -/
def czApply {nq : Nat} (a b : Fin nq) (es : ErrorState nq) : ErrorState nq where
  paulis := fun i =>
    if i = a then pauliMul (if hasXComp (es.paulis b) then Pauli.Z else Pauli.I) (es.paulis a)
    else if i = b then pauliMul (if hasXComp (es.paulis a) then Pauli.Z else Pauli.I) (es.paulis b)
    else es.paulis i
  measFlips := es.measFlips

section Checks
private def cz01 : Circuit 3 := czCircuit (0 : Fin 3) 1 (by decide)
private def e (q : Fin 3) (p : Pauli) : ErrorState 3 := (ErrorState.clean 3).inject q p

-- X on control a=0 ⇒ X_a Z_b
example : (propagateCircuit cz01 (e 0 .X)).paulis 0 = .X := by decide
example : (propagateCircuit cz01 (e 0 .X)).paulis 1 = .Z := by decide
-- Y on a ⇒ Y_a Z_b (Y has an X-component)
example : (propagateCircuit cz01 (e 0 .Y)).paulis 1 = .Z := by decide
-- Z on a ⇒ unchanged (no X-component)
example : (propagateCircuit cz01 (e 0 .Z)).paulis 0 = .Z := by decide
example : (propagateCircuit cz01 (e 0 .Z)).paulis 1 = .I := by decide
-- X on target b=1 ⇒ Z_a X_b (symmetric)
example : (propagateCircuit cz01 (e 1 .X)).paulis 0 = .Z := by decide
example : (propagateCircuit cz01 (e 1 .X)).paulis 1 = .X := by decide
-- gadget agrees with the closed-form rule on these inputs
example : (propagateCircuit cz01 (e 0 .X)).paulis 0 = (czApply 0 1 (e 0 .X)).paulis 0 := by decide
example : (propagateCircuit cz01 (e 0 .X)).paulis 1 = (czApply 0 1 (e 0 .X)).paulis 1 := by decide
example : (propagateCircuit cz01 (e 1 .X)).paulis 0 = (czApply 0 1 (e 1 .X)).paulis 0 := by decide
end Checks

end QStab.QClifford
