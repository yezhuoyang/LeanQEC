import QStab.QClifford.Compile.SurfaceNZStabTransport
import QStab.QClifford.Compile.SurfaceHValid

/-!
# F1 Stab-half: the bar-Z circuit-level distance floor, PCC-slot shaped

This file closes the packaging of the F1 Stab-half against the *landed* circuit-level
distance geometry.  The two ingredients:

* `surfaceNZ_logicalFailure_iff` (this milestone): the PCC `logicalFailure` obligation is a
  source-side `(Centralizer ∧ ¬ InStab)` statement over `mkSurfaceQECParams`;
* `surface_compiled_barZ_distance` (already proven): a clean-start run of the compiled
  Surface/NZ circuit whose data residual is a bar-Z logical fired at least `d` faults.

The bridge between them is *geometric*: a `barZClass` member commutes with every stabilizer
(the `Centralizer` half, by definition of the class) and anticommutes with `Z̄`, hence is not
a stabilizer product (`barZ_parityZ_not_InStab`, the `¬ InStab` half — the normalizer/parity
argument).  Composing gives `surfaceNZ_ftDistance_barZ`: for a bar-Z-type logical residual,
the compiled circuit both witnesses a PCC `logicalFailure` **and** meets the `d`-fault floor.

## Coverage gap (honest)

This is the `ftDistance` slot obligation *restricted to bar-Z-type logical residuals*.  The
full slot quantifies over **all** `logicalFailure`s; the nonzero-syndrome centralizer that is
not a stabilizer decomposes as `barZ ∪ barX (∪ barY)` cosets, and F1 delivers only the `barZ`
inclusion.  The `barX` coset (`X̄`-type logicals) is the subject of milestone **F3**
(`mkSurfaceLogicalX` + the column-cut telescope); until F3 lands, `surfaceNZ_ftDistance_barZ`
is *not* the full `ftDistance` slot and must not be presented as such.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.QClifford.PCC.SurfaceNZ
open QStab.Examples.SurfaceParametric
open QHL.AssertionLang
open QHL.Source.Examples.Surface
open QHL.Source.Examples.SurfaceUnionSpec

/-- **Parity-with-`Z̄` ⇒ not a stabilizer** (the `¬ InStab` half, named).  A data residual
that anticommutes with the surface logical `Z̄` (`mkSurfaceLogicalZ`) cannot be a stabilizer
product: every `InStab` element lies in the normalizer of `Z̄`
(`logicalZ_normalizer_parametric`: each generator commutes with `Z̄`), so by `ErrorVec.parity`
F₂-bilinearity (`InStab.parity_of_normalizer`) it commutes with `Z̄` — contradicting the
anticommutation. -/
theorem barZ_parityZ_not_InStab (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (E : ErrorVec (d * d)) (hZ : ErrorVec.parity (mkSurfaceLogicalZ d) E = true) :
    ¬ InStab (mkSurfaceQECParams d hd hodd) E := by
  intro hInStab
  have hfalse : ErrorVec.parity (mkSurfaceLogicalZ d) E = false := by
    rw [ErrorVec.parity_symm]
    exact QStab.InStab.parity_of_normalizer
      (fun i => logicalZ_normalizer_parametric d hd i) hInStab
  rw [hfalse] at hZ
  exact absurd hZ (by decide)

/-- **F1 Stab-half — the bar-Z `ftDistance` floor (slot-shaped).**  For every clean-start run
of the compiled Surface/NZ circuit whose data residual is a bar-Z logical, the residual is a
genuine PCC `logicalFailure` **and** the run fired at least `d` faults.  This is the
`ftDistance` slot obligation restricted to the bar-Z coset (see the coverage-gap note at the
top of the file). -/
theorem surfaceNZ_ftDistance_barZ (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (sigma : QCState (d * d + programHelperCount (surfaceXZProgram d hd)))
    (hrun : qceval (compileProgram (surfaceXZProgram d hd))
      (QCState.clean (d * d + programHelperCount (surfaceXZProgram d hd))) sigma)
    (hbarZ : (surfaceLogicalClass d (unionSurfaceSpec d hd3 hodd)).contains
      (dataErrorOfQCState (surfaceUParams d hd3 hodd) (surfaceHelpers d hd) sigma)) :
    QStab.QClifford.PCC.logicalFailure (fullProgramCodeSpecD (surfaceXZProgram d hd)
        (fullProgramReadoutDisjoint_auto (surfaceXZProgram d hd)) d hd) sigma.es
      ∧ d ≤ sigma.lambda := by
  refine ⟨?_, surface_compiled_barZ_distance d hd hd3 hodd sigma hrun hbarZ⟩
  rw [surfaceNZ_logicalFailure_iff d hd hd3 hodd sigma]
  obtain ⟨hCent, hZ⟩ :=
    (alignedBarZ_contains_iff (unionSurfaceSpec d hd3 hodd).toAligned _).mp hbarZ
  exact ⟨hCent, barZ_parityZ_not_InStab d hd hodd _ hZ⟩

end QStab.QClifford.Compile
