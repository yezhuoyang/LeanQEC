import QStab.QClifford.Compile.SurfaceNZReachHeven
import QStab.QClifford.Compile.StabTransportCore
import QStab.QClifford.Compile.SurfaceNZSpecAlign
import QStab.QClifford.Compile.SurfaceNZVCGen
import QStab.QClifford.Compile.SurfaceNZFtDistance

/-!
# F2 reach: the outer fold and the discharged reach slot

Composes `reach_step` across the compiled surface program's gadget blocks: starting from
the clean state, running the full compiled circuit on `surfaceReachScript` leaves the
column-0 logical `X̄` on the data block with every detector quiet and exactly `d` fired
faults.  The induction walks the block list of `programMeasuresAt (surfaceXZProgram d hd)`
(the `compileProgramAux_eq_flatMap_programMeasuresAtAux` decomposition), peeling one gadget
per step with the unconditional `runFScript_append`/`runFScript_take_errLoc` splitters and
advancing the stage invariant `ReachState (colPrefixB d (stageAt d k))` via `reach_step`.

The headline `surfaceNZ_vcgen_reachD` packages `reach_run` into the PCC `reach` VCSlot: the
count conjunct is `reach_run.2` (the spec's `d` is definitional), and `failure` splits into
`logicalFailure` (the data residual is `mkSurfaceAttackerX = X̄`, routed through
`surfaceNZ_logicalFailure_iff` with `mkSurfaceAttackerX_commutes_with_stabilizers` /
`barZ_parityZ_not_InStab`) and `allFlagsZero` (immediate from `ReachState.det`).  Surface now
passes 4/5 VCGen slots (programEq/wf/syn/reach); `ftDistance` is the remaining X-side work.

**HGP-G3 note.**  HGP's remaining reach obligation is a near-copy of this file: the generic
block calculus (`reach_step`, `runFScript_nzBlock`, `lifted_slot_ne_anc`/`lifted_nodup`, now
in `NZReachCalculus`) is code-agnostic; only the per-kind `injs_k`/`stageAt`/`heven` decode and
this packaging change per code.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.QClifford.PCC.SurfaceNZ
open QStab.Examples.SurfaceParametric
open QHL.Source.Examples.SurfaceParametricUpperBound

/-- Every block of the compiled surface program is an NZ gadget (list form). -/
theorem surfaceXZProgram_map_scheme (d : Nat) (hd : 0 < d) :
    (programMeasuresAt (surfaceXZProgram d hd)).map (·.scheme)
      = (List.finRange (numStabFormula d)).map (fun _ => Scheme.NZ) := by
  unfold programMeasuresAt surfaceXZProgram
  exact measuresAtAux_seqMeas_map_scheme (nzSchedule d hd) (List.finRange (numStabFormula d))
    0 0 _ _

/-- **The outer reach fold.**  Entering the gadget-list suffix at position `k` with the
stage-`stageAt d k` invariant, running the remaining compiled blocks on the remaining
script segments lands the full-column invariant and fires exactly the remaining
injections. -/
theorem reach_fold (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    ∀ (fuel k : Nat), numStabFormula d - k = fuel → k ≤ numStabFormula d →
    ∀ (es : ErrorState (d * d + programHelperCount (surfaceXZProgram d hd))),
      ReachState (colPrefixB d (stageAt d k)) es →
      ReachState (colPrefixB d (stageAt d (numStabFormula d)))
          (runFScript
            (((programMeasuresAt (surfaceXZProgram d hd)).drop k).flatMap
              (fun m => compileGadgetBlock m.scheme m.schedule m.helperStart m.helperFit))
            (((List.finRange (numStabFormula d)).drop k).flatMap
              (fun j => surfaceReachSegment d j.val))
            es).1
        ∧ (runFScript
            (((programMeasuresAt (surfaceXZProgram d hd)).drop k).flatMap
              (fun m => compileGadgetBlock m.scheme m.schedule m.helperStart m.helperFit))
            (((List.finRange (numStabFormula d)).drop k).flatMap
              (fun j => surfaceReachSegment d j.val))
            es).2 = stageAt d (numStabFormula d) - stageAt d k := by
  intro fuel
  induction fuel with
  | zero =>
      intro k hfuel hk es hR
      have hkeq : k = numStabFormula d := by omega
      subst hkeq
      have hlen : (programMeasuresAt (surfaceXZProgram d hd)).length = numStabFormula d :=
        programNumStab_surfaceXZProgram d hd
      have h1 : (programMeasuresAt (surfaceXZProgram d hd)).drop (numStabFormula d) = [] :=
        List.drop_eq_nil_of_le (le_of_eq hlen)
      have h2 : (List.finRange (numStabFormula d)).drop (numStabFormula d) = [] :=
        List.drop_eq_nil_of_le (le_of_eq List.length_finRange)
      rw [h1, h2]
      simp only [List.flatMap_nil, runFScript]
      exact ⟨hR, (Nat.sub_self _).symm⟩
  | succ fuel ih =>
      intro k hfuel hk es hR
      have hklt : k < numStabFormula d := by omega
      have hlen : (programMeasuresAt (surfaceXZProgram d hd)).length = numStabFormula d :=
        programNumStab_surfaceXZProgram d hd
      have hklt' : k < (programMeasuresAt (surfaceXZProgram d hd)).length := by
        rw [hlen]; exact hklt
      have hkltf : k < (List.finRange (numStabFormula d)).length := by
        rw [List.length_finRange]; exact hklt
      -- peel the head block and the head segment
      have hdropms : (programMeasuresAt (surfaceXZProgram d hd)).drop k
          = (programMeasuresAt (surfaceXZProgram d hd))[k]
            :: (programMeasuresAt (surfaceXZProgram d hd)).drop (k + 1) :=
        List.drop_eq_getElem_cons hklt'
      have hgetf : (List.finRange (numStabFormula d))[k]'hkltf = ⟨k, hklt⟩ := by
        apply Fin.ext; simp [List.getElem_finRange]
      have hdropf : (List.finRange (numStabFormula d)).drop k
          = (⟨k, hklt⟩ : Fin (numStabFormula d))
            :: (List.finRange (numStabFormula d)).drop (k + 1) := by
        rw [List.drop_eq_getElem_cons hkltf, hgetf]
      -- head facts: scheme and schedule
      have hscheme : (programMeasuresAt (surfaceXZProgram d hd))[k].scheme = Scheme.NZ := by
        have h := congrArg (fun l => l[k]?) (surfaceXZProgram_map_scheme d hd)
        simp only [List.getElem?_map, List.getElem?_eq_getElem hklt',
          List.getElem?_eq_getElem hkltf, Option.map_some] at h
        exact Option.some.injEq _ _ ▸ h
      have hsched : (programMeasuresAt (surfaceXZProgram d hd))[k].schedule
          = nzSchedule d hd ⟨k, hklt⟩ := by
        have h := congrArg (fun l => l[k]?) (surfaceXZProgram_map_schedule d hd)
        simp only [List.getElem?_map, List.getElem?_eq_getElem hklt',
          List.getElem?_eq_getElem hkltf, Option.map_some, hgetf] at h
        exact Option.some.injEq _ _ ▸ h
      rw [hdropms, hdropf, List.flatMap_cons, List.flatMap_cons]
      -- destructure the head block record so the dependent fit can be rewritten
      rcases hmk : (programMeasuresAt (surfaceXZProgram d hd))[k] with
        ⟨sch, sched, hstart, dstart, hfit, dfit⟩
      rw [hmk] at hscheme hsched
      simp only at hscheme hsched
      subst hscheme
      subst hsched
      -- the head block is the generic nzBlock on the block ancilla
      rw [compileGadgetBlock_NZ_eq_nzBlock]
      set anc := blockHelperQ (d * d) (programHelperCount (surfaceXZProgram d hd)) hstart 1
        hfit ⟨0, Nat.one_pos⟩ with hancdef
      have hanc : d * d ≤ anc.val := by
        simp only [hancdef, blockHelperQ]; omega
      set slots := (liftSchedule (k := programHelperCount (surfaceXZProgram d hd))
        (nzSchedule d hd ⟨k, hklt⟩)).slots with hslots
      have hne : ∀ slot ∈ slots, slot.qubit ≠ anc :=
        lifted_slot_ne_anc _ anc hanc
      have hnodup : (slots.map (·.qubit)).Nodup :=
        lifted_nodup _ (nzSchedule_support_nodup d hd hd3 hodd ⟨k, hklt⟩)
      -- the head segment is the generic blockScript
      have hsegdec : surfaceReachSegment d (⟨k, hklt⟩ : Fin (numStabFormula d)).val
          = blockScript slots (injs_k d k) :=
        surfaceReachSegment_decode d hd (programHelperCount (surfaceXZProgram d hd)) ⟨k, hklt⟩
      rw [hsegdec]
      -- split the run at the head block
      rw [runFScript_append]
      have hcnt : errLocCount (nzBlock anc slots) = (blockScript slots (injs_k d k)).length :=
        errLocCount_nzBlock anc slots (injs_k d k) hne
      have hhead : runFScript (nzBlock anc slots)
          (blockScript slots (injs_k d k)
            ++ ((List.finRange (numStabFormula d)).drop (k + 1)).flatMap
              (fun j => surfaceReachSegment d j.val)) es
          = runFScript (nzBlock anc slots) (blockScript slots (injs_k d k)) es :=
        runFScript_take_errLoc _ _ _ es (le_of_eq hcnt)
      have hdropscript : (blockScript slots (injs_k d k)
            ++ ((List.finRange (numStabFormula d)).drop (k + 1)).flatMap
              (fun j => surfaceReachSegment d j.val)).drop (errLocCount (nzBlock anc slots))
          = ((List.finRange (numStabFormula d)).drop (k + 1)).flatMap
              (fun j => surfaceReachSegment d j.val) := by
        rw [hcnt]; exact List.drop_left
      rw [hhead, hdropscript]
      -- fire the per-gadget step
      obtain ⟨hR', hcount⟩ := reach_step d hd hd3 hodd
        (programHelperCount (surfaceXZProgram d hd)) ⟨k, hklt⟩ anc hanc hne hnodup es hR
      -- retype at the bare index k so every arithmetic atom matches (Fin.val trap)
      have hcount' : (runFScript (nzBlock anc slots) (blockScript slots (injs_k d k)) es).2
          = injRows d k := hcount
      have hR'' : ReachState (colPrefixB d (stageAt d (k + 1)))
          (runFScript (nzBlock anc slots) (blockScript slots (injs_k d k)) es).1 := hR'
      -- recurse on the suffix
      obtain ⟨hRfin, hcntfin⟩ := ih (k + 1) (by omega) (by omega) _ hR''
      refine ⟨hRfin, ?_⟩
      rw [hcount', hcntfin]
      have hsucc : stageAt d (k + 1) = stageAt d k + injRows d k := stageAt_succ d k
      have hmono : stageAt d (k + 1) ≤ stageAt d (numStabFormula d) :=
        stageAt_mono d (by omega)
      omega

/-- **Full-circuit reach run**: from the clean state, the compiled surface program run on
`surfaceReachScript` leaves the full-column residual (the logical `X̄` support) on the data
block with every detector quiet, firing exactly `d` faults. -/
theorem reach_run (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    ReachState (colPrefixB d d)
        (runFScript (compileProgram (surfaceXZProgram d hd)) (surfaceReachScript d hd)
          (ErrorState.clean (d * d + programHelperCount (surfaceXZProgram d hd)))).1
      ∧ (runFScript (compileProgram (surfaceXZProgram d hd)) (surfaceReachScript d hd)
          (ErrorState.clean (d * d + programHelperCount (surfaceXZProgram d hd)))).2 = d := by
  have hprog : compileProgram (surfaceXZProgram d hd)
      = (programMeasuresAt (surfaceXZProgram d hd)).flatMap
          (fun m => compileGadgetBlock m.scheme m.schedule m.helperStart m.helperFit) :=
    compileProgramAux_eq_flatMap_programMeasuresAtAux 0 0 (surfaceXZProgram d hd) _ _
  have hscript : surfaceReachScript d hd
      = (List.finRange (numStabFormula d)).flatMap (fun j => surfaceReachSegment d j.val) :=
    rfl
  have hclean : ReachState (colPrefixB d (stageAt d 0))
      (ErrorState.clean (d * d + programHelperCount (surfaceXZProgram d hd))) := by
    refine ⟨fun q' => ?_, fun _ _ => rfl, fun _ => rfl⟩
    have hb : colPrefixB d (stageAt d 0) q' = false := by
      simp [colPrefixB, stageAt_zero]
    rw [hb]; rfl
  have h0 := reach_fold d hd hd3 hodd (numStabFormula d) 0 rfl (Nat.zero_le _) _ hclean
  rw [List.drop_zero, List.drop_zero] at h0
  rw [hprog, hscript]
  obtain ⟨hRf, hcnt⟩ := h0
  refine ⟨?_, ?_⟩
  · have hxs : colPrefixB d (stageAt d (numStabFormula d)) = colPrefixB d d := by
      rw [stageAt_total d hd3 hodd]
    exact hxs ▸ hRf
  · rw [hcnt, stageAt_zero, stageAt_total d hd3 hodd]
    omega

/-- `foldr xor false` of an all-`false` list is `false`. -/
private theorem foldr_xor_false_of_forall {L : List Bool} (h : ∀ b ∈ L, b = false) :
    L.foldr xor false = false := by
  induction L with
  | nil => rfl
  | cons b bs ih =>
    rw [List.foldr_cons, h b (List.mem_cons.mpr (Or.inl rfl)), Bool.false_xor]
    exact ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

/-- **The surface `reach` VCSlot, discharged.**  Packaging `reach_run`: the compiled Surface/NZ
circuit run on `surfaceReachScript` fires exactly `d` faults and lands a genuine `failure`
(logical `X̄` residual with every flag quiet).  Surface passes 4/5 VCGen slots. -/
theorem surfaceNZ_vcgen_reachD (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (hnq : 0 < d * d + programHelperCount (surfaceXZProgram d hd))
    (hnumStab : 0 < programNumStab (surfaceXZProgram d hd)) :
    (vcgen (generatedFullProgramVCInputD (surfaceXZProgram d hd) d hd hnq hnumStab)).denoteSlot
      .reach (surfaceReachScript d hd) := by
  obtain ⟨hReach, hCount⟩ := reach_run d hd hd3 hodd
  have htc : (generatedFullProgramVCInputD (surfaceXZProgram d hd) d hd hnq hnumStab).toCodeSpec
      = fullProgramCodeSpecD (surfaceXZProgram d hd)
          (fullProgramReadoutDisjoint_auto (surfaceXZProgram d hd)) d hd := by
    simp only [generatedFullProgramVCInputD, fullProgramVCInputD, VCInput.toCodeSpec_ofPCC]
  have hpr : (generatedFullProgramVCInputD (surfaceXZProgram d hd) d hd hnq hnumStab).program
      = compileProgram (surfaceXZProgram d hd) := rfl
  simp only [GeneratedVCs.denoteSlot, VCSlot.denote, htc, hpr]
  set esf := (runFScript (compileProgram (surfaceXZProgram d hd)) (surfaceReachScript d hd)
      (ErrorState.clean (d * d + programHelperCount (surfaceXZProgram d hd)))).1 with hesf
  refine ⟨hCount, ?_, ?_, ?_⟩
  · -- logicalFailure: the data residual is X̄, which commutes with all stabilizers and is not one
    set sig : QCState (d * d + programHelperCount (surfaceXZProgram d hd)) := ⟨esf, d⟩ with hsig
    rw [surfaceNZ_logicalFailure_iff d hd hd3 hodd sig]
    have hde : dataErrorOfQCState (mkSurfaceQECParams d hd hodd)
        (programHelperCount (surfaceXZProgram d hd)) sig = mkSurfaceAttackerX d := by
      funext q
      show esf.paulis (freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd)) q)
        = mkSurfaceAttackerX d q
      rw [hReach.data q, xOfBool_colPrefixB]
      exact congrFun (colPrefix_d_eq_attackerX d) q
    simp only [hde]
    exact ⟨fun j => mkSurfaceAttackerX_commutes_with_stabilizers d hd hodd j,
      barZ_parityZ_not_InStab d hd hodd _ (mkSurfaceAttackerX_anticommutes_logicalZ d hd)⟩
  · -- undetected: all detectors quiet, so every syndrome bit is the xor of falses
    intro i
    simp only [syndromeBit, xorBools]
    exact foldr_xor_false_of_forall (fun b hb => by
      obtain ⟨f, _, rfl⟩ := List.mem_map.mp hb; exact hReach.det _)
  · -- allPostselectionFlagsZero: immediate from ReachState.det
    intro i _; exact hReach.det _

/-- info: 'QStab.QClifford.Compile.surfaceNZ_vcgen_reachD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms surfaceNZ_vcgen_reachD

/-- The ambient-dimension positivity side condition (`0 < n`), discharged. -/
theorem surfaceXZ_nq_pos (d : Nat) (hd : 0 < d) :
    0 < d * d + programHelperCount (surfaceXZProgram d hd) := by
  have : 0 < d * d := Nat.mul_pos hd hd
  omega

/-- The stabilizer-count positivity side condition (`0 < numStab`), discharged. -/
theorem surfaceXZ_numStab_pos (d : Nat) (hd : 0 < d) :
    0 < programNumStab (surfaceXZProgram d hd) := by
  rw [programNumStab_surfaceXZProgram]; unfold numStabFormula; omega

/-- **Canonical surface reach slot** (HGP-form): `surfaceNZ_vcgen_reachD` with the two
positivity side conditions discharged internally. -/
theorem surfaceXZ_vcgen_reachD (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    (vcgen (generatedFullProgramVCInputD (surfaceXZProgram d hd) d hd
        (surfaceXZ_nq_pos d hd) (surfaceXZ_numStab_pos d hd))).denoteSlot
      .reach (surfaceReachScript d hd) :=
  surfaceNZ_vcgen_reachD d hd hd3 hodd _ _

end QStab.QClifford.Compile
