import QStab.Paper.AlignedBarrier

/-!
# Surface code as a `BarrierFunction` instance (paper §7)

Specialises the generic aligned-code barrier
(`Paper/AlignedBarrier.lean`) to the rotated surface code under
NZ scheduling. The instance wraps `NZSurfaceSpec d` via the
existing `NZSurfaceSpec.toAligned` conversion and inherits the
generic construction.

Paper references: Definition `def:PerpSpread`, Corollary
`thm:PerpBarrier`, Theorem `thm:intro_surface`.

**Zero sorry; only [propext, Classical.choice, Quot.sound] axioms.**
-/

namespace QStab.Paper.SurfaceBarrier

open QStab QStab.Examples QStab.Examples.SurfaceGeneral
     QStab.Paper.BarrierFramework QStab.Paper.AlignedBarrier

variable {d : Nat}

/-- The bar-Z logical class for an `NZSurfaceSpec`, defined via
    `NZSurfaceSpec.toAligned`. -/
def barZClass (spec : NZSurfaceSpec d) : LogicalClass spec.params :=
  AlignedBarrier.barZClass spec.toAligned

/-- The surface code's perpendicular-spread barrier function for the
    bar-Z coset. -/
noncomputable def surfaceBarrier (spec : NZSurfaceSpec d) :
    BarrierFunction spec.params (barZClass spec) :=
  AlignedBarrier.alignedBarrier spec.toAligned

/-- NZ scheduling is L-aligned for the surface barrier. -/
theorem surface_isLAligned (spec : NZSurfaceSpec d) :
    IsLAligned (surfaceBarrier spec) :=
  AlignedBarrier.aligned_isLAligned spec.toAligned

/-- **Surface code distance preservation as a `BarrierFunction` instance.**
    For any `NZSurfaceSpec d`, the surface code under NZ scheduling
    satisfies `C_budget − C ≥ d` at any done state with an undetected
    bar-Z (or bar-Y) logical error. The chain
    `topological_lower_bound + perpendicular spread + hook_spread_bound`
    is now visible as `mu_at_logical + mu_triangle + IsLAligned`. -/
theorem surface_distance_preservation (spec : NZSurfaceSpec d)
    (s : State spec.params)
    (hrun : Run spec.params (.done s))
    (h_in : (barZClass spec).contains s.E_tilde) :
    spec.params.C_budget - s.C ≥ d :=
  distance_preservation (surfaceBarrier spec) (surface_isLAligned spec)
    s hrun h_in

end QStab.Paper.SurfaceBarrier
