import QStab.QClifford.Compile.SurfaceNZAssembly
import QStab.QClifford.Compile.HGPNZProgram
import QStab.QHL.Source.Examples.HGPUnionSpec

/-!
# Assembly: compiled HGP bar-Z distance, conditional on `HGPHValid`

The HGP instance of the fixed compiled-distance bridge, wired verbatim over
the union source machine at budget `d` (`exactUnionHGPSpec`):

* the parametric source invariant certificate (`hgp_invariant_certificate`,
  spec-parametric),
* the preservation bridge (`etildeC_hoare_preservation` + `hFold_of_valid` +
  `barrier_hMatch` — reused, never re-derived),
* the distance extraction (`compiled_barrier_distance`, with the generic
  `alignedBarZ_barrier_eval_zero` as `hmu` and `Nat.le_refl d` as `hbudget`
  after the budget-`d` retarget),

leaving exactly **one** obligation open: `HGPHValid` — every fault site of
the compiled HGP circuit has a weight-`≤ 1` data residual or an
in-back-action-set hook.  The statements mention only `HGP.code` (through
`hgpXZProgram`) and `compileProgram`.

Unlike the surface (odd `d ≥ 3`), the HGP family needs only `d ≥ 2`: no
NZ-geometry parity is involved — hook alignment is the tensor structure.
-/

namespace QStab.QClifford.Compile

open QStab
open QStab.QClifford
open QHL
open QHL.AssertionLang
open QHL.Source.Examples.HGP
open QHL.Source.Examples.HGPUnionSpec

/-- The compiled HGP circuit — the compilation of the generator-defined
    program, never hand-written. -/
def hgpCircuit (d : Nat) :
    FCircuit ((d * d + (d - 1) * (d - 1)) + programHelperCount (hgpXZProgram d)) :=
  compileProgram (hgpXZProgram d)

/-- Ambient QEC params of the bridge: the HGP union machine at budget `d`. -/
abbrev hgpUParams (d : Nat) (hd : 2 ≤ d) : QECParams :=
  (exactUnionHGPSpec d hd).params

/-- Helper-qubit count of the compiled HGP program. -/
abbrev hgpHelpers (d : Nat) : Nat := programHelperCount (hgpXZProgram d)

/-- **The single remaining obligation.**  Every fault site of the compiled
HGP circuit either has a weight-`≤ 1` data residual or its residual is a hook
in the (union) back-action set — at every state, provable over the union
machine because its `backActionSet` ignores the current stabilizer. -/
def HGPHValid (d : Nat) (hd : 2 ≤ d) : Prop :=
  ∀ f : FiredFaultWithContext ((hgpUParams d hd).n + hgpHelpers d),
    f.site ∈ QStab.QClifford.PCC.errLocsWithContextAux
      (QCState.clean ((hgpUParams d hd).n + hgpHelpers d)).es.detectorCursor
      (hgpCircuit d) →
    ErrorVec.weight (targetFaultDataResidual (hgpUParams d hd) f) ≤ 1 ∨
      ∀ st' : State (hgpUParams d hd),
        targetFaultDataResidual (hgpUParams d hd) f ∈
          (hgpUParams d hd).backActionSet
            (currentStab (hgpProgram d (exactUnionHGPSpec d hd)) st')

/-- **Conditional compiled invariant.**  The compiled HGP circuit satisfies
the budget-guarded compiled barrier invariant, given `HGPHValid`. -/
theorem hgpNZ_compiled_FHoare (d : Nat) (hd : 2 ≤ d) (hv : HGPHValid d hd) :
    FHoare
      (fun sigma : QCState ((hgpUParams d hd).n + hgpHelpers d) =>
        sigma = QCState.clean ((hgpUParams d hd).n + hgpHelpers d))
      (hgpCircuit d)
      (compileFormulaWithinBudget (hgpHelpers d)
        (hgp_inv_formula d (exactUnionHGPSpec d hd))) :=
  etildeC_hoare_preservation
    (hgp_invariant_certificate d (exactUnionHGPSpec d hd))
    (fun _ hrun hb => hFold_of_valid hrun hb hv)
    (fun st sigma hE hC hb hden => barrier_hMatch _ _ st sigma hE hC hb hden)

/-- **Conditional compiled bar-Z distance.**  Every clean-start run of
`compileProgram (hgpXZProgram d)` whose data residual lies in the bar-Z
logical class fired at least `d` faults — for every `d ≥ 2`, any gate
scheduling of the per-check couplings having been absorbed into the union
back-action set. -/
theorem hgpNZ_compiled_barZ_distance (d : Nat) (hd : 2 ≤ d) (hv : HGPHValid d hd) :
    ∀ sigma : QCState ((hgpUParams d hd).n + hgpHelpers d),
      qceval (hgpCircuit d)
        (QCState.clean ((hgpUParams d hd).n + hgpHelpers d)) sigma →
      (hgpLogicalClass d (exactUnionHGPSpec d hd)).contains
        (dataErrorOfQCState (hgpUParams d hd) (hgpHelpers d) sigma) →
      d ≤ sigma.lambda :=
  compiled_barrier_distance
    (hgpNZ_compiled_FHoare d hd hv)
    (fun E hE => alignedBarZ_barrier_eval_zero "hgp.beta" "hgp.rows" "hgp.barZ"
      (exactUnionHGPSpec d hd).toAligned E hE)
    (Nat.le_refl d)

#print axioms hgpNZ_compiled_FHoare
#print axioms hgpNZ_compiled_barZ_distance

end QStab.QClifford.Compile
