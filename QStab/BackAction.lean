import QStab.State

/-! # Back-action error characterization

The back-action error set B¹(T_s) is a field of `QECParams`, so each code
can supply its own concrete set. This file provides the convenience alias
`backActionSet` and re-exports the weight bound from `QECParams`.
-/

namespace QStab

/-- Convenience alias: the back-action set for stabilizer `s` in code `P`.
    This is just `P.backActionSet s`. -/
abbrev backActionSet (P : QECParams) (s : Fin P.numStab) : Set (ErrorVec P.n) :=
  P.backActionSet s

/-- Every back-action error in B¹(T_s) has Hamming weight ≤ r.
    This delegates to the `QECParams` field. -/
theorem backAction_weight_bound (P : QECParams) (s : Fin P.numStab)
    (e : ErrorVec P.n) (he : e ∈ backActionSet P s) :
    ErrorVec.weight e ≤ P.r :=
  P.backAction_weight_bound s e he

end QStab
