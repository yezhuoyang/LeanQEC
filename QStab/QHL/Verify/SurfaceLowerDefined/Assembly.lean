import QStab.QHL.Verify.SurfaceLowerDefined.ColWeight

/-!
# Lower bound — Assembly

Assembly of the nine core well-formedness lemmas into the `DefinedObligations` the
prover's `lowerDefined` field consumes.  Includes core 3 (`distanceLowerBoundBody_WF`,
the top-level ∧-intro of the two nontrivial-normaliser facts) and the entry point
`lowerDefinedAux`.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-- Core 3: `distanceLowerBoundBodyFromFamilyLemmasDeriv` WF — `simpa`-wrapped `andIntro` of two
`impIntro`s; the `impIntro` antecedents are `x/zNontrivialNormalizerF` (FD via the helpers above);
the `mp`/`weakenContext`/`assumption`/`hyp` subtree is structurally trivial. -/
theorem distanceLowerBoundBody_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    DerivWF (distanceLowerBoundBodyFromFamilyLemmasDeriv D) Surface.code.body
      (bridgeProofFuel D) Env.empty E := by
  have hX : SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (OpenStab.xNontrivialNormalizerF D) :=
    formulaDefined_and (formulaDefined_normalizesOdd D hTotal)
      (formulaDefined_anticommutesLogicalZ D hTotal)
  have hZ : SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (OpenStab.zNontrivialNormalizerF D) :=
    formulaDefined_and (formulaDefined_normalizesOdd D hTotal)
      (formulaDefined_anticommutesLogicalX D hTotal)
  unfold distanceLowerBoundBodyFromFamilyLemmasDeriv
  simp only [id_eq]
  -- `andIntro` of two `impIntro`s; each child is `mp`/`weakenContext`/`assumption`/`hyp` (all `True`)
  exact ⟨⟨hX, fun _ => ⟨trivial, trivial, trivial⟩⟩, ⟨hZ, fun _ => ⟨trivial, trivial, trivial⟩⟩⟩

/-- **The lower-bound definedness assembly** — matches the prover's `lowerDefined`
goal exactly: from `width.eval = some n` and `TotalUpTo n E`, discharge the six leaves'
obligations, threading `hTotal` (with `n = nQubits`) to the nine core WFs. -/
theorem lowerDefinedAux (D : OddSurfaceDistance) (E : PartialStabilizer) (n : Nat)
    (hWidth : (distanceLowerBoundForallStabF D).width.eval Surface.code.body
      (bridgeProofFuel D) Env.empty E = some n)
    (hTotal : TotalUpTo n E) :
    (PureLowerClosedLeaves.lowerBound (mkL D)).DefinedObligations E := by
  have hn : nQubits D.distance = n := by
    simpa [distanceLowerBoundForallStabF, scn_eval] using hWidth
  subst hn
  refine pfd_defined _ E ?_
  exact ⟨distanceLowerBoundBody_WF D hTotal,
    ⟨xParityPropRowsCore_WF D hTotal, rowCutNoX_WF D hTotal, rowCutTelescoping_WFP D E,
      ⟨rowBridgeFactorsNorm_WF D hTotal, rowBridgeGenerated_WFP D E, rowStripRange_WFP D E⟩⟩,
    xRowsWeight_WF D hTotal,
    ⟨zParityPropColsCore_WF D hTotal, colCutNoZ_WF D hTotal, colCutTelescoping_WFP D E,
      ⟨colBridgeFactorsNorm_WF D hTotal, colBridgeGenerated_WFP D E, colStripRange_WFP D E⟩⟩,
    zColsWeight_WF D hTotal⟩

end QHL.CodeLang.Surface.Verify
