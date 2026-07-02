import QStab.QClifford.PCC.SurfaceNZ

/-!
# Code anchor: the QStab stabilizer family is `Surface.code`'s content

The QStab machine (`mkSurfaceQECParams` → `NZSurfaceSpec` → source certificate →
compiled distance theorem) defines its stabilizers through the meta decoder
`decodeStabPauliAt`.  The certified definition of the surface code is the recursive
object-language program `Surface.code`, whose evaluation is proven (for every odd
distance) to equal the flat classifier `surfaceCellPauli`
(`recCall_eval_surfaceCellPauli`).  This file closes the identification:

  `mkSurfaceStabilizers d hd i q = surfaceCellPauli d i.val q.val`

so every stabilizer the machine measures — and hence everything compiled from it —
is *provably* the code defined by `Surface.code`, not a parallel re-definition.
-/

namespace QStab.QClifford.Compile

open QStab QStab.Examples.SurfaceParametric
open QHL.CodeLang.Surface.Verify

/-- The QStab stabilizer count is the code-level count `d² − 1`. -/
theorem numStabFormula_eq_sq_sub_one (d : Nat) (hd2 : 2 ≤ d) :
    numStabFormula d = d * d - 1 := by
  cases d with
  | zero => omega
  | succ m =>
      have hm : 1 ≤ m := by omega
      have hge : 1 ≤ m * m + 2 * m := by omega
      have hexp : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
      simp only [numStabFormula, Nat.succ_sub_one, hexp, Nat.max_eq_right hge]

/-- **The code anchor.**  The machine's stabilizer family is pointwise the certified
code-language classifier: for every in-range stabilizer index and qubit,
`decodeStabPauliAt` agrees with `surfaceCellPauli` — which is in turn the proven
evaluation of `Surface.code` at every odd distance
(`recCall_eval_surfaceCellPauli`, `SurfaceCharEval.lean`). -/
theorem mkSurfaceStabilizers_eq_surfaceCellPauli (d : Nat) (hd : 0 < d) (hd2 : 2 ≤ d)
    (i : Fin (numStabFormula d)) (q : Fin (d * d)) :
    mkSurfaceStabilizers d hd i q = surfaceCellPauli d i.val q.val := by
  have hk : i.val < d * d - 1 := by
    have hlt := i.isLt
    have heq := numStabFormula_eq_sq_sub_one d hd2
    omega
  show decodeStabPauliAt d i.val (q.val / d) (q.val % d) = surfaceCellPauli d i.val q.val
  simp only [decodeStabPauliAt, surfaceCellPauli, inBulkBand, bulkKind,
    cellRow, cellCol, cellR, cellC, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq]
  split_ifs <;> first | rfl | omega

end QStab.QClifford.Compile
