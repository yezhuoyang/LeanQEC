import QStab.QClifford.Compile.XZProgramOfProgramsSurface
import QStab.QClifford.Compile.XZProgramOfProgramsLeaves
import QStab.QClifford.Compile.SurfaceHValid
import QStab.QClifford.Compile.HGPKnillAssembly
import QStab.QClifford.Compile.CompiledHvalidGeneric

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

/-! ## The scheme-generic surface bar-Z bridge (verbatim, over the surface union machine)

Everything above the per-gadget classification — the union source machine, its
invariant certificate, the barrier, and the `compiled_barrier_distance` bridge —
is consumed **verbatim** (scheme-independently), exactly as the surface/NZ family
does.  A scheme closes the compiled surface bar-Z floor by supplying a
`SurfaceSchemeHValid` (its per-fault-site classification over the *scheme's*
compiled circuit); the bridge is proved once here. -/

open QHL QHL.AssertionLang
open QHL.Source.Examples.Surface QHL.Source.Examples.SurfaceUnionSpec

/-- Helper-qubit count of a scheme's compiled surface program. -/
abbrev surfaceSchemeHelpers (scheme : Scheme) (d : Nat) : Nat :=
  programHelperCount (surfaceSchemeProgram scheme d)

/-- A scheme's compiled surface circuit. -/
def surfaceSchemeCircuit (scheme : Scheme) (d : Nat) :
    FCircuit ((d * d) + surfaceSchemeHelpers scheme d) :=
  compileProgram (surfaceSchemeProgram scheme d)

/-- **The scheme's hvalid obligation** — identical shape to `SurfaceHValid`, over
the scheme's compiled circuit; the abstract program / union back-action set are
unchanged (scheme-independent). -/
def SurfaceSchemeHValid (scheme : Scheme) (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) : Prop :=
  ∀ f : FiredFaultWithContext ((surfaceUParams d hd3 hodd).n + surfaceSchemeHelpers scheme d),
    f.site ∈ QStab.QClifford.PCC.errLocsWithContextAux
      (QCState.clean ((surfaceUParams d hd3 hodd).n + surfaceSchemeHelpers scheme d)).es.detectorCursor
      (surfaceSchemeCircuit scheme d) →
    ErrorVec.weight (targetFaultDataResidual (surfaceUParams d hd3 hodd) f) ≤ 1 ∨
      ∀ st' : State (surfaceUParams d hd3 hodd),
        targetFaultDataResidual (surfaceUParams d hd3 hodd) f ∈
          (surfaceUParams d hd3 hodd).backActionSet
            (currentStab (surfaceProgram d (unionSurfaceSpec d hd3 hodd)) st')

/-- **Generic compiled invariant** — the verbatim bridge, over the scheme circuit. -/
theorem surfaceScheme_compiled_FHoare (scheme : Scheme) (d : Nat) (_hd : 0 < d)
    (hd3 : 3 ≤ d) (hodd : d % 2 = 1) (hv : SurfaceSchemeHValid scheme d hd3 hodd) :
    FHoare
      (fun sigma : QCState ((surfaceUParams d hd3 hodd).n + surfaceSchemeHelpers scheme d) =>
        sigma = QCState.clean ((surfaceUParams d hd3 hodd).n + surfaceSchemeHelpers scheme d))
      (surfaceSchemeCircuit scheme d)
      (compileFormulaWithinBudget (surfaceSchemeHelpers scheme d)
        (surface_inv_formula d (unionSurfaceSpec d hd3 hodd))) :=
  etildeC_hoare_preservation
    (surface_invariant_certificate d (unionSurfaceSpec d hd3 hodd))
    (fun _ hrun hb => hFold_of_valid hrun hb hv)
    (fun st sigma hE hC hb hden => barrier_hMatch _ _ st sigma hE hC hb hden)

/-- **Generic compiled surface bar-Z distance.**  Every clean-start run of a
scheme's compiled surface circuit whose data residual is bar-Z fired `≥ d`
faults — given the scheme's `SurfaceSchemeHValid`, through the unchanged bridge. -/
theorem surfaceScheme_compiled_barZ_distance (scheme : Scheme) (d : Nat) (hd : 0 < d)
    (hd3 : 3 ≤ d) (hodd : d % 2 = 1) (hv : SurfaceSchemeHValid scheme d hd3 hodd) :
    ∀ sigma : QCState ((surfaceUParams d hd3 hodd).n + surfaceSchemeHelpers scheme d),
      qceval (surfaceSchemeCircuit scheme d)
        (QCState.clean ((surfaceUParams d hd3 hodd).n + surfaceSchemeHelpers scheme d)) sigma →
      (surfaceLogicalClass d (unionSurfaceSpec d hd3 hodd)).contains
        (dataErrorOfQCState (surfaceUParams d hd3 hodd) (surfaceSchemeHelpers scheme d) sigma) →
      d ≤ sigma.lambda :=
  compiled_barrier_distance
    (surfaceScheme_compiled_FHoare scheme d hd hd3 hodd hv)
    (fun E hE => alignedBarZ_barrier_eval_zero "surface.beta" "surface.rows" "surface.barZ"
      (unionSurfaceSpec d hd3 hodd).toAligned E hE)
    (Nat.le_refl d)

/-! ## Knill is an instance of the surface framework (transversal → weight ≤ 1)

Knill extraction is transversal: every fault has a data residual of weight `≤ 1`,
`code-independently` (`knill_site_wle1`).  So the hook branch is never taken and
the surface union back-action set is never needed — the compiled surface bar-Z
floor closes for Knill by reusing the *same* code-generic transversality lemma the
HGP/Knill family uses. -/

/-- **The surface `LeafClean` witness for Knill** — reusing the code-generic
`knillBlock_cab`/`knillBlock_PDA` through `surfaceSchemeProgram_measLeaf`. -/
theorem surfaceKnill_leafClean (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    LeafClean (total := surfaceSchemeHelpers Scheme.Knill d)
      (surfaceSchemeProgram Scheme.Knill d) := by
  intro sc sg hml st hf
  obtain ⟨i, rfl, rfl⟩ := surfaceSchemeProgram_measLeaf Scheme.Knill d hd hd3 hodd sc sg hml
  exact ⟨knillBlock_cab _ _ _, knillBlock_PDA _ _ _⟩

/-- **The surface Knill hvalid** — every fault site is weight `≤ 1` (transversal),
so `SurfaceSchemeHValid` holds with the hook branch unused. -/
theorem surfaceKnill_hvalid (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    SurfaceSchemeHValid Scheme.Knill d hd3 hodd :=
  compiled_hvalid_of_classifier (P := surfaceUParams d hd3 hodd)
    (surfaceSchemeProgram Scheme.Knill d)
    (fun R => ∀ st' : State (surfaceUParams d hd3 hodd),
      R ∈ (surfaceUParams d hd3 hodd).backActionSet
        (currentStab (surfaceProgram d (unionSurfaceSpec d hd3 hodd)) st'))
    (surfaceKnill_leafClean d hd hd3 hodd)
    (fun scheme sigma gstart gcursor gtail ghfit hML hpres site p hp hsite => by
      -- Knill weight-≤ 1 holds for *any* schedule; we only need `scheme = .Knill`
      -- (the leaf pin), so `sigma` stays abstract over `P.n` — exactly as
      -- `knill_SchemeClassifier`, keeping every bound in the single atom `P.n`.
      obtain ⟨_, rfl, -⟩ :=
        surfaceSchemeProgram_measLeaf Scheme.Knill d hd hd3 hodd scheme sigma hML
      left
      rw [compileGadgetBlock_Knill_eq] at hsite
      refine knill_site_wle1 gtail
        ((surfaceUParams d hd3 hodd).n + gstart + helperCount Scheme.Knill sigma)
        (by omega) hpres
        ((liftSchedule (k := surfaceSchemeHelpers Scheme.Knill d) sigma).slots.zip
          (blockHelpers (surfaceUParams d hd3 hodd).n (surfaceSchemeHelpers Scheme.Knill d)
            gstart sigma.slots.length ghfit))
        ?_ ?_ ?_ gcursor site p hp hsite
      · intro pc hpc; exact (knill_zip_facts sigma gstart ghfit pc hpc).1
      · intro pc hpc; have := (knill_zip_facts sigma gstart ghfit pc hpc).2.1; omega
      · intro pc hpc
        have := (knill_zip_facts sigma gstart ghfit pc hpc).2.2
        have hw : helperCount Scheme.Knill sigma = sigma.slots.length := rfl
        rw [hw]; omega)

/-- **The Knill-extraction compiled surface bar-Z distance** — surface closes
under Knill, through the framework and the verbatim bridge, reusing the
code-generic transversal weight-`≤ 1` classifier. -/
theorem surfaceKnill_compiled_barZ_distance (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) :
    ∀ sigma : QCState ((surfaceUParams d hd3 hodd).n + surfaceSchemeHelpers Scheme.Knill d),
      qceval (surfaceSchemeCircuit Scheme.Knill d)
        (QCState.clean ((surfaceUParams d hd3 hodd).n + surfaceSchemeHelpers Scheme.Knill d)) sigma →
      (surfaceLogicalClass d (unionSurfaceSpec d hd3 hodd)).contains
        (dataErrorOfQCState (surfaceUParams d hd3 hodd) (surfaceSchemeHelpers Scheme.Knill d) sigma) →
      d ≤ sigma.lambda :=
  surfaceScheme_compiled_barZ_distance Scheme.Knill d hd hd3 hodd
    (surfaceKnill_hvalid d hd hd3 hodd)

/-- info: 'QStab.QClifford.Compile.surfaceKnill_compiled_barZ_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms surfaceKnill_compiled_barZ_distance

end QStab.QClifford.Compile
