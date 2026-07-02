import QStab.QClifford.Compile.ETildeCDistance
import QStab.QClifford.PCC.SurfaceNZ
import QStab.QHL.Source.Examples.SurfaceUnionSpec

/-!
# Assembly: compiled Surface/NZ bar-Z distance, conditional on `SurfaceHValid`

This file wires the whole parametric pipeline together over the union source
machine (`unionSurfaceSpec`):

* the parametric source invariant certificate (`surface_invariant_certificate`),
* the preservation bridge (`etildeC_hoare_preservation` + `hFold_of_valid` +
  `barrier_hMatch`),
* the distance extraction (`compiled_barrier_distance`),

leaving exactly **one** obligation open: `SurfaceHValid` — every fault site of
the compiled circuit has a weight-`≤ 1` data residual or an in-back-action-set
hook.  Proving `SurfaceHValid` (piece 2) immediately yields the unconditional
`surfaceNZ_compiled_barZ_distance`.

`SurfaceHValid` is stated once, as a named `Prop`, so the downstream theorems
cannot drift from the obligation actually being proved.
-/

namespace QStab.QClifford.Compile

open QStab
open QStab.QClifford
open QHL
open QHL.AssertionLang
open QHL.Source.Examples.Surface
open QHL.Source.Examples.SurfaceUnionSpec
open QStab.QClifford.PCC.SurfaceNZ

/-- **Barrier vanishes on the symbolic bar-Z class** (generic aligned-code form).
The `hmu` input of `compiled_barrier_distance`, extracted from the `logical`
leaf recipe of `BarrierContractCertificate.ofAlignedSpreadCodeSpec`. -/
theorem alignedBarZ_barrier_eval_zero {d : Nat} (betaName geomName lName : String)
    (spec : QStab.Examples.SurfaceGeneral.AlignedCodeSpec d)
    (E : ErrorVec spec.params.n)
    (hE : (LogicalClassSymbol.ofAlignedBarZ lName spec).contains E) :
    (BarrierSymbol.ofAlignedCodeSpec betaName geomName spec).eval E = 0 := by
  rw [BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier]
  exact (QStab.Paper.AlignedBarrier.alignedBarrier spec).mu_at_logical E
    ((alignedBarZ_contains_iff spec E).mp hE)

/-- Ambient QEC params of the bridge: the union machine at budget `d`. -/
abbrev surfaceUParams (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) : QECParams :=
  (unionSurfaceSpec d hd3 hodd).params

/-- Helper-qubit count of the compiled surface program. -/
abbrev surfaceHelpers (d : Nat) (hd : 0 < d) : Nat :=
  programHelperCount (surfaceXZProgram d hd)

/-- **The single remaining obligation (piece 2).**  Every fault site of the
compiled Surface/NZ circuit either has a weight-`≤ 1` data residual or its
residual is a hook in the (union) back-action set — at every state, which is
provable over the union machine because its `backActionSet` ignores the
current stabilizer. -/
def SurfaceHValid (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) : Prop :=
  ∀ f : FiredFaultWithContext
      ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd),
    f.site ∈ QStab.QClifford.PCC.errLocsWithContextAux
      (QCState.clean ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd)).es.detectorCursor
      (surfaceCircuit d hd) →
    ErrorVec.weight (targetFaultDataResidual (surfaceUParams d hd3 hodd) f) ≤ 1 ∨
      ∀ st' : State (surfaceUParams d hd3 hodd),
        targetFaultDataResidual (surfaceUParams d hd3 hodd) f ∈
          (surfaceUParams d hd3 hodd).backActionSet
            (currentStab (surfaceProgram d (unionSurfaceSpec d hd3 hodd)) st')

/-- **Piece 3, conditional.**  The compiled Surface/NZ circuit satisfies the
budget-guarded compiled barrier invariant, given `SurfaceHValid`. -/
theorem surfaceNZ_compiled_FHoare (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) (hv : SurfaceHValid d hd hd3 hodd) :
    FHoare
      (fun sigma : QCState ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd) =>
        sigma = QCState.clean ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd))
      (surfaceCircuit d hd)
      (compileFormulaWithinBudget (surfaceHelpers d hd)
        (surface_inv_formula d (unionSurfaceSpec d hd3 hodd))) :=
  etildeC_hoare_preservation
    (surface_invariant_certificate d (unionSurfaceSpec d hd3 hodd))
    (fun _ hrun hb => hFold_of_valid hrun hb hv)
    (fun st sigma hE hC hb hden => barrier_hMatch _ _ st sigma hE hC hb hden)

/-- **Piece 4a, conditional.**  Compiled bar-Z circuit-level distance: every
clean-start run of the compiled Surface/NZ circuit whose data residual lies in
the bar-Z logical class fired at least `d` faults. -/
theorem surfaceNZ_compiled_barZ_distance (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) (hv : SurfaceHValid d hd hd3 hodd) :
    ∀ sigma : QCState ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd),
      qceval (surfaceCircuit d hd)
        (QCState.clean ((surfaceUParams d hd3 hodd).n + surfaceHelpers d hd)) sigma →
      (surfaceLogicalClass d (unionSurfaceSpec d hd3 hodd)).contains
        (dataErrorOfQCState (surfaceUParams d hd3 hodd) (surfaceHelpers d hd) sigma) →
      d ≤ sigma.lambda :=
  compiled_barrier_distance
    (surfaceNZ_compiled_FHoare d hd hd3 hodd hv)
    (fun E hE => alignedBarZ_barrier_eval_zero "surface.beta" "surface.rows" "surface.barZ"
      (unionSurfaceSpec d hd3 hodd).toAligned E hE)
    (Nat.le_refl d)

end QStab.QClifford.Compile
