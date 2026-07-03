import QStab.QClifford.Compile.HGPShorAssembly

/-!
# Scheme-generic compiled HGP bar-Z distance framework

Everything above the per-gadget site classification is proved **once**, generic
in the measurement `Scheme`.  A scheme closes the compiled HGP bar-Z distance by
supplying exactly two per-scheme facts about its *syntactic* compilation
(`compileGadgetBlock scheme …`):

* `LeafClean (hgpSchemeProgram scheme d)` — its gadget block acts below its
  helper ceiling and preserves data from clean helpers, and
* `SchemeClassifier scheme` — every fault site of its gadget block has a
  weight-`≤ 1` data residual or one that is `dominatedByScheduleHook`.

Given those, `hgpScheme_hvalid` discharges the unconditional `HGPHValid`-shaped
obligation and `hgpScheme_compiled_barZ_distance` closes the floor through the
**verbatim** bridge (the same union source machine, invariant certificate,
barrier, and `compiled_barrier_distance` the NZ/Shor families use).  The proof
goes through `compileProgram (hgpSchemeProgram scheme d)` — the actual scheme
compilation — never a re-defined lower-level circuit.
-/

namespace QStab.QClifford.Compile

open QStab
open QStab.QClifford
open QHL
open QHL.CodeHGPSchedule
open QHL.Source.Examples.HGP
open QHL.Source.Examples.HGPUnionSpec
open QStab.Examples.HGPParametric

/-- The compiled-source HGP program for a given extraction scheme: the same
code-blind generator over `HGP.code`, measuring each stabilizer via `scheme`. -/
def hgpSchemeProgram (scheme : Scheme) (d : Nat) : XZProgram (d * d + (d - 1) * (d - 1)) :=
  xzProgramOfProgramsWith scheme QHL.CodeLang.HGP.code hgpOrderProg hgpLenProg
    (2 * ((d - 1) * d)) (d * d + (d - 1) * (d - 1)) d

/-- Every measurement leaf of `hgpSchemeProgram scheme d` is
`(scheme, hgpSchedule d hd i)` — the generic generator pin specialized through
the certified `genSchedule_eq_hgpSchedule`. -/
theorem hgpSchemeProgram_measLeaf (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (sc : Scheme) (sigma : RuleSchedule (d * d + (d - 1) * (d - 1))) :
    MeasLeaf (hgpSchemeProgram scheme d) sc sigma →
      ∃ i : Fin (2 * ((d - 1) * d)), sc = scheme ∧ sigma = hgpSchedule d hd i := by
  intro h
  unfold hgpSchemeProgram at h
  obtain ⟨k, hk, hs, hσ⟩ :=
    xzProgramOfProgramsWith_measLeaf scheme QHL.CodeLang.HGP.code hgpOrderProg hgpLenProg
      (2 * ((d - 1) * d)) (d * d + (d - 1) * (d - 1)) d sc sigma h
  exact ⟨⟨k, hk⟩, hs, hσ.trans (genSchedule_eq_hgpSchedule d hd ⟨k, hk⟩)⟩

/-- Helper-qubit count of a scheme's compiled HGP program. -/
abbrev hgpSchemeHelpers (scheme : Scheme) (d : Nat) : Nat :=
  programHelperCount (hgpSchemeProgram scheme d)

/-- A scheme's compiled HGP circuit. -/
def hgpSchemeCircuit (scheme : Scheme) (d : Nat) :
    FCircuit ((d * d + (d - 1) * (d - 1)) + hgpSchemeHelpers scheme d) :=
  compileProgram (hgpSchemeProgram scheme d)

/-- **The reusable per-gadget classification interface.**  A scheme satisfies
this when every fault site of its (syntactic) compiled gadget block has a
weight-`≤ 1` data residual or a `dominatedByScheduleHook` one — the exact form
`shor_gadget_site_classified` proves, with the conditional `PreservesDataAbove`
tail. -/
def SchemeClassifier (scheme : Scheme) : Prop :=
  ∀ {P : QECParams} {total : Nat} (sigma : RuleSchedule P.n) (kk : XZPauli),
    (∀ s ∈ sigma.slots, s.kind = kk) → (sigma.slots.map (·.qubit)).Nodup →
    ∀ (gstart : Nat) (ghfit : gstart + helperCount scheme sigma ≤ total)
      (tail : FCircuit (P.n + total)),
      PreservesDataAbove (eraseFaults tail) (P.n + gstart + helperCount scheme sigma) →
      ∀ (cursor : Nat) (site : PCC.ErrLocWithContext (P.n + total)) (p : Pauli) (hp : p ≠ Pauli.I),
        site ∈ prefixErrLocsWithContextAux cursor
          (compileGadgetBlock scheme sigma gstart ghfit) tail →
        ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≤ 1 ∨
          dominatedByScheduleHook sigma (targetFaultDataResidual P ⟨site, p, hp⟩)

/-- **The scheme's hvalid obligation** — identical shape to `HGPHValid`, over
the scheme's compiled circuit; the abstract program / union back-action set are
unchanged (scheme-independent). -/
def HGPSchemeHValid (scheme : Scheme) (d : Nat) (hd : 2 ≤ d) : Prop :=
  ∀ f : FiredFaultWithContext ((hgpUParams d hd).n + hgpSchemeHelpers scheme d),
    f.site ∈ QStab.QClifford.PCC.errLocsWithContextAux
      (QCState.clean ((hgpUParams d hd).n + hgpSchemeHelpers scheme d)).es.detectorCursor
      (hgpSchemeCircuit scheme d) →
    ErrorVec.weight (targetFaultDataResidual (hgpUParams d hd) f) ≤ 1 ∨
      ∀ st' : State (hgpUParams d hd),
        targetFaultDataResidual (hgpUParams d hd) f ∈
          (hgpUParams d hd).backActionSet
            (currentStab (hgpProgram d (exactUnionHGPSpec d hd)) st')

/-- **Generic hvalid discharge.**  Given a scheme's `LeafClean` witness and its
`SchemeClassifier`, the unconditional hvalid obligation holds for every `d ≥ 2`.
Site split (generic, via the `LeafClean` witness) → leaf pin → classifier →
domination — the same skeleton as `hgpShor_hvalid`, now scheme-parametric. -/
theorem hgpScheme_hvalid (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (hleaf : LeafClean (total := hgpSchemeHelpers scheme d) (hgpSchemeProgram scheme d))
    (hclass : SchemeClassifier scheme) :
    HGPSchemeHValid scheme d hd := by
  intro f hf
  obtain ⟨site, p, hp⟩ := f
  rw [errLocsWithContextAux_eq_prefix_nil] at hf
  obtain ⟨sc, sigma, gstart, gcursor, gtail, ghfit, hML, hPDAtail, hsite⟩ :=
    compileProgramAux_site_split_gen (total := hgpSchemeHelpers scheme d)
      (hgpSchemeProgram scheme d) hleaf 0 (by simp) _ [] site
      (by intro es _ dd _; simp [eraseFaults, propagateCircuit]) hf
  obtain ⟨i, rfl, rfl⟩ := hgpSchemeProgram_measLeaf scheme d hd sc sigma hML
  have hclassed := hclass (P := hgpUParams d hd) (hgpSchedule d hd i) (hgpKind d i.val)
    (hgpSchedule_kind_uniform d hd i) (hgpSchedule_support_nodup d hd i)
    gstart ghfit gtail hPDAtail gcursor site p hp hsite
  rcases hclassed with hle | hdom
  · exact Or.inl hle
  · refine Or.inr fun _ => ?_
    exact ⟨⟨i.val, i.isLt⟩, fun q => dominatedByScheduleHook_hgp d hd i _ hdom q⟩

/-- **Generic compiled invariant** — the verbatim bridge. -/
theorem hgpScheme_compiled_FHoare (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (hv : HGPSchemeHValid scheme d hd) :
    FHoare
      (fun sigma : QCState ((hgpUParams d hd).n + hgpSchemeHelpers scheme d) =>
        sigma = QCState.clean ((hgpUParams d hd).n + hgpSchemeHelpers scheme d))
      (hgpSchemeCircuit scheme d)
      (compileFormulaWithinBudget (hgpSchemeHelpers scheme d)
        (hgp_inv_formula d (exactUnionHGPSpec d hd))) :=
  etildeC_hoare_preservation
    (hgp_invariant_certificate d (exactUnionHGPSpec d hd))
    (fun _ hrun hb => hFold_of_valid hrun hb hv)
    (fun st sigma hE hC hb hden => barrier_hMatch _ _ st sigma hE hC hb hden)

/-- **Generic compiled HGP bar-Z distance.**  Every clean-start run of a
scheme's compiled HGP circuit whose data residual is bar-Z fired `≥ d` faults,
for every `d ≥ 2`, through the unchanged bridge — given the scheme's `LeafClean`
witness and `SchemeClassifier`. -/
theorem hgpScheme_compiled_barZ_distance (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (hv : HGPSchemeHValid scheme d hd) :
    ∀ sigma : QCState ((hgpUParams d hd).n + hgpSchemeHelpers scheme d),
      qceval (hgpSchemeCircuit scheme d)
        (QCState.clean ((hgpUParams d hd).n + hgpSchemeHelpers scheme d)) sigma →
      (hgpLogicalClass d (exactUnionHGPSpec d hd)).contains
        (dataErrorOfQCState (hgpUParams d hd) (hgpSchemeHelpers scheme d) sigma) →
      d ≤ sigma.lambda :=
  compiled_barrier_distance
    (hgpScheme_compiled_FHoare scheme d hd hv)
    (fun E hE => alignedBarZ_barrier_eval_zero "hgp.beta" "hgp.rows" "hgp.barZ"
      (exactUnionHGPSpec d hd).toAligned E hE)
    (Nat.le_refl d)

/-! ## Shor is an instance of the framework -/

/-- `shor_gadget_site_classified` is exactly a `SchemeClassifier .Shor`. -/
theorem shor_SchemeClassifier : SchemeClassifier Scheme.Shor :=
  fun sigma kk hkind hnd gstart ghfit tail htailPDA cursor site p hp hsite =>
    shor_gadget_site_classified sigma kk hkind hnd gstart ghfit tail htailPDA cursor site p hp hsite

/-- The Shor bar-Z floor, re-derived through the generic framework. -/
theorem hgpShor_compiled_barZ_distance_framework (d : Nat) (hd : 2 ≤ d) :
    ∀ sigma : QCState ((hgpUParams d hd).n + hgpSchemeHelpers Scheme.Shor d),
      qceval (hgpSchemeCircuit Scheme.Shor d)
        (QCState.clean ((hgpUParams d hd).n + hgpSchemeHelpers Scheme.Shor d)) sigma →
      (hgpLogicalClass d (exactUnionHGPSpec d hd)).contains
        (dataErrorOfQCState (hgpUParams d hd) (hgpSchemeHelpers Scheme.Shor d) sigma) →
      d ≤ sigma.lambda :=
  hgpScheme_compiled_barZ_distance Scheme.Shor d hd
    (hgpScheme_hvalid Scheme.Shor d hd (hgpShor_leafClean d hd) shor_SchemeClassifier)

/-- info: 'QStab.QClifford.Compile.hgpScheme_hvalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hgpScheme_hvalid

/--
info: 'QStab.QClifford.Compile.hgpScheme_compiled_barZ_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpScheme_compiled_barZ_distance

end QStab.QClifford.Compile
