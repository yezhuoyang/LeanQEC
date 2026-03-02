import QStab.State

/-! # Back-action error characterization

Defines the back-action error set B¹(T_s) and the weight bound axiom.
The precise definition of B¹ depends on the circuit model and is left abstract.
-/

namespace QStab

/-- The set of back-action errors from a single syndrome qubit of stabilizer s.
    B¹(T_s) in the paper: n-qubit Pauli errors caused by a faulty CNOT
    during syndrome extraction. Left abstract (axiomatized by weight bound). -/
def backActionSet (P : QECParams) (s : Fin P.numStab) : Set (ErrorVec P.n) :=
  sorry

/-- Axiom: the weight of any back-action error from B¹(T_s) is bounded by r. -/
axiom backAction_weight_bound (P : QECParams) (s : Fin P.numStab)
    (e : ErrorVec P.n) (he : e ∈ backActionSet P s) :
    ErrorVec.weight e ≤ P.r

end QStab
