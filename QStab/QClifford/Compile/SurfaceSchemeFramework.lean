import QStab.QClifford.Compile.XZProgramOfProgramsSurface
import QStab.QClifford.Compile.XZProgramOfProgramsLeaves

/-!
# Scheme-generic compiled Surface program (the generator re-anchor, scheme-parametric)

The surface analog of `hgpSchemeProgram` / `hgpSchemeProgram_measLeaf`: the same
code-blind generator (`xzProgramOfProgramsWith`) over `Surface.code` with the
surface object programs `nzOrderProg` / `nzLenProg`, measuring each of the
`d*d - 1` stabilizers via an arbitrary extraction `Scheme`.

For `scheme = .NZ` this reproduces the hand-built `surfaceXZProgram d hd` exactly
(`xzProgramOfPrograms_surface_eq`).  Every measurement leaf is the surface NZ
schedule `nzSchedule d hd i` (via the certified `genSchedule_eq_nzSchedule`) — the
scheme-parametric leaf pin the generic site-split / classification stack consumes.

This file lands only the **program + leaf pin** (the mechanical, code-generic
foundation, through the syntactic generator).  The full scheme closure (hvalid →
bar-Z floor) additionally needs a surface union spec whose back-action set is the
scheme-uniform `dominatedByScheduleHook`-shaped one (the coarse "dominated by a
stabilizer generator" predicate that `SchemeClassifier` concludes and HGP's
`hgpBackAction` already uses), together with that spec's `hook_spread_bound`.  The
surface certificate currently ships `hook_spread_bound` only for the *finer*
`mkSurfaceHookErrors` (NZ suffix-hook) set, so that swap is genuine
surface-geometric work, tracked separately.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford
open QStab.QClifford.PCC.SurfaceNZ
open QStab.Examples.SurfaceParametric
open QHL.CodeLang
open QHL.CodeLang.Surface
open QHL.CodeSurfaceSchedule

/-- The compiled-source surface program for a given extraction scheme: the same
code-blind generator over `Surface.code` with the surface object programs, measuring
each of the `d*d - 1` stabilizers via `scheme`.  For `.NZ` it is definitionally the
hand-built `surfaceXZProgram` (`xzProgramOfPrograms_surface_eq`). -/
def surfaceSchemeProgram (scheme : Scheme) (d : Nat) : XZProgram (d * d) :=
  xzProgramOfProgramsWith scheme Surface.code nzOrderProg nzLenProg
    (d * d - 1) (d * d) d

/-- Every measurement leaf of `surfaceSchemeProgram scheme d` is
`(scheme, nzSchedule d hd i)` — the generic generator leaf pin specialized through
the certified `genSchedule_eq_nzSchedule`. -/
theorem surfaceSchemeProgram_measLeaf (scheme : Scheme) (d : Nat) (hd : 0 < d)
    (hd3 : 3 ≤ d) (hodd : d % 2 = 1) (sc : Scheme) (sigma : RuleSchedule (d * d)) :
    MeasLeaf (surfaceSchemeProgram scheme d) sc sigma →
      ∃ i : Fin (numStabFormula d), sc = scheme ∧ sigma = nzSchedule d hd i := by
  intro h
  unfold surfaceSchemeProgram at h
  obtain ⟨k, hk, hs, hσ⟩ :=
    xzProgramOfProgramsWith_measLeaf scheme Surface.code nzOrderProg nzLenProg
      (d * d - 1) (d * d) d sc sigma h
  have hknum : k < numStabFormula d := by
    have := numStabFormula_eq_sq_sub_one d (by omega)
    omega
  refine ⟨⟨k, hknum⟩, hs, ?_⟩
  rw [hσ]
  exact genSchedule_eq_nzSchedule d hd hd3 hodd ⟨k, hknum⟩

/-- info: 'QStab.QClifford.Compile.surfaceSchemeProgram_measLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms surfaceSchemeProgram_measLeaf

end QStab.QClifford.Compile
