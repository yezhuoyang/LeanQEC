import QStab.Paper.AlignedBarrier

/-!
# HGP codes as a `BarrierFunction` instance (paper §8)

Specialises the generic aligned-code barrier
(`Paper/AlignedBarrier.lean`) to hypergraph-product codes. The
instance wraps `HGPSpec d` via `HGPSpec.toAligned` and inherits
the generic construction. Unlike the surface code, HGP codes
satisfy hook alignment automatically from their tensor-product
structure (paper Lemma `lem:HGPHookAlign`), so `IsLAligned` holds
under *any* gate scheduling.

Paper references: Definition `def:ColSpread`, Corollary
`thm:HGPColBarrier`, Theorem `thm:intro_hgp`.

**Zero sorry; only [propext, Classical.choice, Quot.sound] axioms.**
-/

namespace QStab.Paper.HGPBarrier

open QStab QStab.Examples QStab.Examples.SurfaceGeneral
     QStab.Paper.BarrierFramework QStab.Paper.AlignedBarrier

variable {d : Nat}

/-- The bar-Z logical class for an `HGPSpec`, defined via
    `HGPSpec.toAligned`. -/
def barZClass (spec : HGPSpec d) : LogicalClass spec.params :=
  AlignedBarrier.barZClass spec.toAligned

/-- The HGP code's column-spread barrier function for the bar-Z coset. -/
noncomputable def hgpBarrier (spec : HGPSpec d) :
    BarrierFunction spec.params (barZClass spec) :=
  AlignedBarrier.alignedBarrier spec.toAligned

/-- HGP code is L-aligned for the column-spread barrier under any gate
    scheduling (the tensor-product structure makes hooks automatically
    column-aligned, paper Lemma `lem:HGPHookAlign`). -/
theorem hgp_isLAligned (spec : HGPSpec d) :
    IsLAligned (hgpBarrier spec) :=
  AlignedBarrier.aligned_isLAligned spec.toAligned

/-- **HGP code distance preservation as a `BarrierFunction` instance.**
    For any `HGPSpec d`, the HGP code under any gate scheduling satisfies
    `C_budget − C ≥ d` at any done state with an undetected bar-Z (or
    bar-Y) logical error. Same proof skeleton as the surface code, with
    the column partition replacing the row partition. -/
theorem hgp_distance_preservation (spec : HGPSpec d)
    (s : State spec.params)
    (hrun : Run spec.params (.done s))
    (h_in : (barZClass spec).contains s.E_tilde) :
    spec.params.C_budget - s.C ≥ d :=
  distance_preservation (hgpBarrier spec) (hgp_isLAligned spec)
    s hrun h_in

end QStab.Paper.HGPBarrier
