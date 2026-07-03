import QStab.QClifford.Compile.SiteSplitGen
import QStab.QClifford.Compile.SurfaceHValid

/-!
# The generic compiled `hvalid`, scheme-agnostic

The compiled-`hvalid` obligation — every fault site of `compileProgram program`
has a weight-`≤ 1` data residual or an absorbable hook — is assembled the same way
for **every** syndrome-extraction scheme:

1. `errLocsWithContextAux_eq_prefix_nil` normalizes the site set;
2. `compileProgramAux_site_split_gen` (over a `LeafClean` witness) splits the site
   into some compiled gadget block `compileGadgetBlock scheme sigma …`;
3. a **per-scheme classifier** classifies that block's sites.

Only step 3 is scheme-specific.  `compiled_hvalid_of_classifier` packages steps
1–2 generically over `{P : QECParams}`, an arbitrary compiled `program`, an
abstract hook predicate `hookOK`, a `LeafClean` witness, and the scheme's
`classify` function.  Each scheme (NZ / Shor / Knill / Flag) becomes a compiled
`hvalid` by supplying its `{LeafClean, classify}` — no bespoke assembly, and the
back-action set (`hookOK`) stays a parameter, never hard-wired.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC

/-- **Generic compiled `hvalid`.**  Given a `LeafClean` witness for `program` and a
per-gadget site classifier — for every compiled gadget block, each fault site's
data residual is weight-`≤ 1` or satisfies the abstract hook predicate `hookOK` —
every fault site of `compileProgram program` is classified.  Scheme-agnostic: the
classifier is the sole per-scheme input, and `hookOK` (the code's back-action
set) is a parameter. -/
theorem compiled_hvalid_of_classifier {P : QECParams} (program : XZProgram P.n)
    (hookOK : ErrorVec P.n → Prop)
    (hleaf : LeafClean (total := programHelperCount program) program)
    (classify : ∀ (scheme : Scheme) (sigma : RuleSchedule P.n) (gstart gcursor : Nat)
        (gtail : FCircuit (P.n + programHelperCount program))
        (ghfit : gstart + helperCount scheme sigma ≤ programHelperCount program),
        MeasLeaf program scheme sigma →
        PreservesDataAbove (eraseFaults gtail) (P.n + gstart + helperCount scheme sigma) →
        ∀ (site : PCC.ErrLocWithContext (P.n + programHelperCount program))
          (p : Pauli) (hp : p ≠ Pauli.I),
          site ∈ prefixErrLocsWithContextAux gcursor
            (compileGadgetBlock scheme sigma gstart ghfit) gtail →
          ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≤ 1 ∨
            hookOK (targetFaultDataResidual P ⟨site, p, hp⟩)) :
    ∀ f : FiredFaultWithContext (P.n + programHelperCount program),
      f.site ∈ QStab.QClifford.PCC.errLocsWithContextAux
        (QCState.clean (P.n + programHelperCount program)).es.detectorCursor
        (compileProgram program) →
      ErrorVec.weight (targetFaultDataResidual P f) ≤ 1 ∨
        hookOK (targetFaultDataResidual P f) := by
  intro f hf
  obtain ⟨site, p, hp⟩ := f
  rw [errLocsWithContextAux_eq_prefix_nil] at hf
  obtain ⟨scheme, sigma, gstart, gcursor, gtail, ghfit, hML, hpres, hsite⟩ :=
    compileProgramAux_site_split_gen program hleaf 0 (by simp) _ [] site
      (fun es _ d _ => rfl) hf
  exact classify scheme sigma gstart gcursor gtail ghfit hML hpres site p hp hsite

end QStab.QClifford.Compile
