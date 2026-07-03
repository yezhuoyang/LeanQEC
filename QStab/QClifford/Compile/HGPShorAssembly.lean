import QStab.QClifford.Compile.HGPHValid
import QStab.QClifford.Compile.ShorClassify
import QStab.QClifford.Compile.ShorLeafClean

/-!
# The compiled Shor-extraction HGP bar-Z distance — the reuse demonstration

`hgpShor_compiled_barZ_distance` closes the Shor-extraction HGP program through
the **unchanged** compiled-distance bridge that the NZ family uses.  Everything
above the site classification is consumed verbatim:

* the source machine is the *same* scheme-independent union spec
  `exactUnionHGPSpec` (the abstract program, invariant certificate, barrier, and
  logical class do not mention the measurement scheme);
* the bridge `etildeC_hoare_preservation` / `hFold_of_valid` /
  `compiled_barrier_distance` is instantiated, never widened;
* only the compiled circuit and its per-gadget classification change:
  `hgpShorCircuit` in place of `hgpCircuit`, `shor_gadget_site_classified` in
  place of `nz_gadget_site_classified`, threaded through the `site_split_gen`
  generalization with the Shor `LeafClean` witness.

The unconditional `HGPHValid`-shaped obligation is satisfiable (the residual
fingerprint confirmed it), so no post-selection restriction enters.
-/

namespace QStab.QClifford.Compile

open QStab
open QStab.QClifford
open QHL
open QHL.CodeHGPSchedule
open QHL.Source.Examples.HGP
open QHL.Source.Examples.HGPUnionSpec
open QStab.Examples.HGPParametric

/-! ## The domination bridge -/

/-- **A schedule hook of the HGP schedule is dominated by its generator.**  If a
residual is `dominatedByScheduleHook` of `hgpSchedule d hd i`, then at every
qubit it is identity or exactly the `i`-th generator's entry — so it lies in
`hgpBackAction d i`.  (The scheduled-qubit → generator step is the same
`scheduleKind_hgpSchedule` + `stabEntry_mem_supportList` core as
`nzSuffixResidual_hgpSchedule_dominated`.) -/
theorem dominatedByScheduleHook_hgp (d : Nat) (hd : 2 ≤ d)
    (i : Fin (2 * ((d - 1) * d))) (R : ErrorVec (d * d + (d - 1) * (d - 1)))
    (h : dominatedByScheduleHook (hgpSchedule d hd i) R)
    (q : Fin (d * d + (d - 1) * (d - 1))) :
    R q = Pauli.I ∨ R q = mkHGPRepStabilizers d ⟨i.val, i.isLt⟩ q := by
  rcases h q with hI | ⟨hval, hmem⟩
  · exact Or.inl hI
  · right
    rw [hval]
    show scheduleKind (hgpSchedule d hd i) = stabEntry d i.val q.val
    obtain ⟨slot, hslot_mem, hslot_q⟩ := List.mem_map.mp hmem
    have hq0 : ∃ q₀ ∈ hgpSupportList d i.val, hgpFin d hd q₀ = slot.qubit := by
      unfold hgpSchedule RuleSchedule.uniform at hslot_mem
      simp only [List.mem_map] at hslot_mem
      obtain ⟨qf, hqf, rfl⟩ := hslot_mem
      obtain ⟨q₀, hq₀, rfl⟩ := hqf
      exact ⟨q₀, hq₀, rfl⟩
    obtain ⟨q₀, hq₀mem, hq₀⟩ := hq0
    have hqval : q.val = q₀ := by
      rw [← hslot_q, ← hq₀]
      show q₀ % (d * d + (d - 1) * (d - 1)) = q₀
      exact Nat.mod_eq_of_lt (hgpSupportList_lt d i.val hd i.isLt q₀ hq₀mem)
    rw [scheduleKind_hgpSchedule d hd i, hqval,
      stabEntry_mem_supportList d i.val q₀ hd i.isLt hq₀mem]

/-! ## The compiled Shor circuit and its `hvalid` obligation -/

/-- Helper-qubit count of the compiled Shor-extraction program. -/
abbrev hgpShorHelpers (d : Nat) : Nat := programHelperCount (hgpShorProgram d)

/-- The compiled Shor-extraction HGP circuit. -/
def hgpShorCircuit (d : Nat) :
    FCircuit ((d * d + (d - 1) * (d - 1)) + hgpShorHelpers d) :=
  compileProgram (hgpShorProgram d)

/-- **The Shor hvalid obligation** — the same shape as `HGPHValid`, over the
Shor circuit; the abstract program / union back-action set are unchanged. -/
def HGPShorHValid (d : Nat) (hd : 2 ≤ d) : Prop :=
  ∀ f : FiredFaultWithContext ((hgpUParams d hd).n + hgpShorHelpers d),
    f.site ∈ QStab.QClifford.PCC.errLocsWithContextAux
      (QCState.clean ((hgpUParams d hd).n + hgpShorHelpers d)).es.detectorCursor
      (hgpShorCircuit d) →
    ErrorVec.weight (targetFaultDataResidual (hgpUParams d hd) f) ≤ 1 ∨
      ∀ st' : State (hgpUParams d hd),
        targetFaultDataResidual (hgpUParams d hd) f ∈
          (hgpUParams d hd).backActionSet
            (currentStab (hgpProgram d (exactUnionHGPSpec d hd)) st')

/-- **`HGPShorHValid` holds for every `d ≥ 2`.**  Site split (generic, via the
Shor `LeafClean` witness) → `.Shor` leaf pin → `shor_gadget_site_classified` →
domination. -/
theorem hgpShor_hvalid (d : Nat) (hd : 2 ≤ d) : HGPShorHValid d hd := by
  intro f hf
  obtain ⟨site, p, hp⟩ := f
  rw [errLocsWithContextAux_eq_prefix_nil] at hf
  obtain ⟨scheme, sigma, gstart, gcursor, gtail, ghfit, hML, hPDAtail, hsite⟩ :=
    compileProgramAux_site_split_gen (total := hgpShorHelpers d) (hgpShorProgram d)
      (hgpShor_leafClean d hd) 0 (by simp) _ [] site
      (by intro es _ dd _; simp [eraseFaults, propagateCircuit]) hf
  obtain ⟨i, rfl, rfl⟩ := hgpShorProgram_measLeaf d hd scheme sigma hML
  have hclass := shor_gadget_site_classified (P := hgpUParams d hd)
    (hgpSchedule d hd i) (hgpKind d i.val)
    (hgpSchedule_kind_uniform d hd i) (hgpSchedule_support_nodup d hd i)
    gstart ghfit gtail hPDAtail gcursor site p hp hsite
  rcases hclass with hle | hdom
  · exact Or.inl hle
  · refine Or.inr fun _ => ?_
    exact ⟨⟨i.val, i.isLt⟩, fun q => dominatedByScheduleHook_hgp d hd i _ hdom q⟩

/-! ## The unchanged bridge -/

/-- **Compiled invariant** for the Shor circuit — same bridge as NZ. -/
theorem hgpShor_compiled_FHoare (d : Nat) (hd : 2 ≤ d) :
    FHoare
      (fun sigma : QCState ((hgpUParams d hd).n + hgpShorHelpers d) =>
        sigma = QCState.clean ((hgpUParams d hd).n + hgpShorHelpers d))
      (hgpShorCircuit d)
      (compileFormulaWithinBudget (hgpShorHelpers d)
        (hgp_inv_formula d (exactUnionHGPSpec d hd))) :=
  etildeC_hoare_preservation
    (hgp_invariant_certificate d (exactUnionHGPSpec d hd))
    (fun _ hrun hb => hFold_of_valid hrun hb (hgpShor_hvalid d hd))
    (fun st sigma hE hC hb hden => barrier_hMatch _ _ st sigma hE hC hb hden)

/-- **The compiled Shor-extraction HGP bar-Z distance** — the reuse
demonstration.  Every clean-start run of `compileProgram (hgpShorProgram d)`
whose data residual lies in the bar-Z logical class fired at least `d` faults,
for every `d ≥ 2`, through the verbatim bridge. -/
theorem hgpShor_compiled_barZ_distance (d : Nat) (hd : 2 ≤ d) :
    ∀ sigma : QCState ((hgpUParams d hd).n + hgpShorHelpers d),
      qceval (hgpShorCircuit d)
        (QCState.clean ((hgpUParams d hd).n + hgpShorHelpers d)) sigma →
      (hgpLogicalClass d (exactUnionHGPSpec d hd)).contains
        (dataErrorOfQCState (hgpUParams d hd) (hgpShorHelpers d) sigma) →
      d ≤ sigma.lambda :=
  compiled_barrier_distance
    (hgpShor_compiled_FHoare d hd)
    (fun E hE => alignedBarZ_barrier_eval_zero "hgp.beta" "hgp.rows" "hgp.barZ"
      (exactUnionHGPSpec d hd).toAligned E hE)
    (Nat.le_refl d)

/-! ## Regression guards (axiom pins) -/

/-- info: 'QStab.QClifford.Compile.hgpShor_hvalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hgpShor_hvalid

/--
info: 'QStab.QClifford.Compile.hgpShor_compiled_barZ_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpShor_compiled_barZ_distance

end QStab.QClifford.Compile
