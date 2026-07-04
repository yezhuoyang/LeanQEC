import QStab.QClifford.Compile.HGPNZReach
import QStab.QClifford.Compile.HGPNZVCGen
import QStab.QClifford.Compile.CodeSafeAssembly
import QStab.QClifford.Compile.HGPReachCommon

/-!
# HGP G3: the reach fold, the discharged `reach` slot, and `hgp_Safe`

The capstone: the row-0 attack script (`hgpReachScript`, kernel-validated in
`HGPNZReach`) is proven correct by a fuel-indexed suffix induction that
re-implements the surface fold pattern (`SurfaceNZReachFold.reach_fold`) —
per-code invariants and side conditions are rebuilt here, not instantiated —
with a **simpler** invariant: the row-prefix `hgpRowB d (min k d)` during the X-phase, constant
full `X̄` through the Z-phase — no stage function beyond `min · d`.

Per-gadget: X-gadgets (all of them, injectors included) are blind to pure-X
residuals (`scheduleParityList_X_uniform`); Z-gadgets measure after all `d`
injections and see the complete `X̄`, quiet by `hgp_Xbar_comm` through the
generic `scheduleParityList_liftSchedule` bridge.

The close packages the run into the `reach` VCSlot through the **public**
`_es` transport forms, and `hgp_Safe` assembles all five discharged slots
into the `DischargedVCs` record consumed by the verifier's `vcgen_sound` —
the first full five-slot `Safe` in the project.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.Examples.HGPParametric
open QHL QHL.CodeHGPSchedule
open QHL.Source.Examples.HGPUnionSpec

/-! ## Program scheme alignment -/

/-- Every block of the compiled HGP program is an NZ gadget (list form). -/
theorem hgpXZProgram_map_scheme (d : Nat) (hd : 2 ≤ d) :
    (programMeasuresAt (hgpXZProgram d)).map (·.scheme)
      = (List.finRange (2 * ((d - 1) * d))).map (fun _ => Scheme.NZ) := by
  rw [hgpXZProgram_eq_foldr d hd]
  unfold programMeasuresAt
  exact measuresAtAux_seqMeas_map_scheme (hgpSchedule d hd)
    (List.finRange (2 * ((d - 1) * d))) 0 0 _ _

/-! ## The row-prefix invariant and per-gadget advance

The scheme-independent row-prefix (`hgpRowB` / `hgpRowPref`, `xOfBool_hgpRowB`,
`hgpRowPref_total`, `hgpInjs_count`, …) and the per-gadget data-advance /
parity-even machinery now live in `HGPReachCommon`, generalized over the ambient
helper count `total` and shared with the Knill reach fold.  Here we re-instantiate
the three ambient-parametric (`_amb`) lemmas that the NZ reach step consumes at
the NZ program's helper count; the reach step below is unchanged. -/

private theorem hgpInjs_length (d : Nat) (hd : 2 ≤ d) (k : Fin (2 * ((d - 1) * d))) :
    (hgpInjs d k.val).length
      = (liftSchedule (k := programHelperCount (hgpXZProgram d))
          (hgpSchedule d hd k)).slots.length :=
  hgpInjs_length_amb d hd k (programHelperCount (hgpXZProgram d))

/-- **Data advance.**  One gadget's entry-site injections move the row-prefix
one column forward (injector `k < d`) or leave it unchanged. -/
private theorem hgp_injectE_advances (d : Nat) (hd : 2 ≤ d)
    (k : Fin (2 * ((d - 1) * d))) :
    injectE (liftSchedule (k := programHelperCount (hgpXZProgram d))
        (hgpSchedule d hd k)).slots (hgpInjs d k.val)
      (dataInputState (k := programHelperCount (hgpXZProgram d))
        (hgpRowPref d k.val)).paulis
    = (dataInputState (k := programHelperCount (hgpXZProgram d))
        (hgpRowPref d (k.val + 1))).paulis :=
  hgp_injectE_advances_amb d hd k (programHelperCount (hgpXZProgram d))

/-- **The side condition**: every gadget's parity check is quiet against the
advanced prefix — X-gadgets by pure-X blindness, Z-gadgets by `hgp_Xbar_comm`
on the completed `X̄`. -/
private theorem hgp_heven (d : Nat) (hd : 2 ≤ d) (k : Fin (2 * ((d - 1) * d))) :
    scheduleParityList (liftSchedule (k := programHelperCount (hgpXZProgram d))
        (hgpSchedule d hd k)).slots
      (injectE (liftSchedule (k := programHelperCount (hgpXZProgram d))
          (hgpSchedule d hd k)).slots (hgpInjs d k.val)
        (dataInputState (k := programHelperCount (hgpXZProgram d))
          (hgpRowPref d k.val)).paulis)
      false = false :=
  hgp_heven_amb d hd k (programHelperCount (hgpXZProgram d))

/-- **The per-gadget reach step**: one compiled block advances the row-prefix
invariant, keeps every detector quiet, and fires `1` fault iff the gadget is
an injector. -/
theorem hgp_reach_step (d : Nat) (hd : 2 ≤ d)
    (k : Fin (2 * ((d - 1) * d)))
    (anc : Fin (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d)))
    (hanc : d * d + (d - 1) * (d - 1) ≤ anc.val)
    (es : ErrorState (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d)))
    (hR : ReachState (hgpRowB d k.val) es) :
    ReachState (hgpRowB d (k.val + 1))
        (runFScript (nzBlock anc (liftSchedule
            (k := programHelperCount (hgpXZProgram d)) (hgpSchedule d hd k)).slots)
          (blockScript (liftSchedule
              (k := programHelperCount (hgpXZProgram d)) (hgpSchedule d hd k)).slots
            (hgpInjs d k.val)) es).1
      ∧ (runFScript (nzBlock anc (liftSchedule
            (k := programHelperCount (hgpXZProgram d)) (hgpSchedule d hd k)).slots)
          (blockScript (liftSchedule
              (k := programHelperCount (hgpXZProgram d)) (hgpSchedule d hd k)).slots
            (hgpInjs d k.val)) es).2
        = (if k.val < d then 1 else 0) := by
  have hne := lifted_slot_ne_anc (total := programHelperCount (hgpXZProgram d))
    (hgpSchedule d hd k) anc hanc
  have hnodup := lifted_nodup (total := programHelperCount (hgpXZProgram d))
    (hgpSchedule d hd k) (hgpSchedule_support_nodup d hd k)
  have hpaulis : es.paulis = (dataInputState
      (k := programHelperCount (hgpXZProgram d)) (hgpRowPref d k.val)).paulis := by
    apply paulis_eq_dataInputState
    · intro q'
      rw [hR.data q', xOfBool_hgpRowB]
    · exact hR.helpers
  have hdata : ∀ q, q ≠ anc → es.paulis q
      = (dataInputState (k := programHelperCount (hgpXZProgram d))
          (hgpRowPref d k.val)).paulis q := fun q _ => congrFun hpaulis q
  obtain ⟨hd1, hanc1, hdet1, hcount⟩ :=
    runFScript_nzBlock anc _ (hgpInjs d k.val) _ es hne hnodup hdata hR.det
      (hgp_heven d hd k)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro q'
    have hfd : freshDataQ (d * d + (d - 1) * (d - 1))
        (programHelperCount (hgpXZProgram d)) q' ≠ anc := by
      intro heq
      have hv := congrArg Fin.val heq
      rw [freshDataQ_val] at hv
      have := q'.isLt
      omega
    rw [hd1 _ hfd, hgp_injectE_advances d hd k, dataInputState_freshDataQ,
      xOfBool_hgpRowB]
  · intro q hq
    by_cases hqa : q = anc
    · rw [hqa]
      exact hanc1
    · rw [hd1 q hqa, hgp_injectE_advances d hd k]
      simp only [dataInputState]
      rw [dif_neg (by omega)]
  · exact hdet1
  · rw [hcount, injCount_eq_count _ _ (hgpInjs_length d hd k), hgpInjs_count]

/-! ## The outer fold and the full-circuit run -/

/-- **The outer reach fold**: entering the gadget-list suffix at position `k`
with the row-prefix invariant, running the remaining blocks on the remaining
script segments completes the prefix and fires the remaining injections. -/
theorem hgp_reach_fold (d : Nat) (hd : 2 ≤ d) :
    ∀ (fuel k : Nat), 2 * ((d - 1) * d) - k = fuel → k ≤ 2 * ((d - 1) * d) →
    ∀ (es : ErrorState (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d))),
      ReachState (hgpRowB d k) es →
      ReachState (hgpRowB d (2 * ((d - 1) * d)))
          (runFScript
            (((programMeasuresAt (hgpXZProgram d)).drop k).flatMap
              (fun m => compileGadgetBlock m.scheme m.schedule m.helperStart m.helperFit))
            (((List.finRange (2 * ((d - 1) * d))).drop k).flatMap
              (fun j => blockScript (liftSchedule
                  (k := programHelperCount (hgpXZProgram d)) (hgpSchedule d hd j)).slots
                (hgpInjs d j.val)))
            es).1
        ∧ (runFScript
            (((programMeasuresAt (hgpXZProgram d)).drop k).flatMap
              (fun m => compileGadgetBlock m.scheme m.schedule m.helperStart m.helperFit))
            (((List.finRange (2 * ((d - 1) * d))).drop k).flatMap
              (fun j => blockScript (liftSchedule
                  (k := programHelperCount (hgpXZProgram d)) (hgpSchedule d hd j)).slots
                (hgpInjs d j.val)))
            es).2 = min (2 * ((d - 1) * d)) d - min k d := by
  intro fuel
  induction fuel with
  | zero =>
      intro k hfuel hk es hR
      have hkeq : k = 2 * ((d - 1) * d) := by omega
      subst hkeq
      have hlen : (programMeasuresAt (hgpXZProgram d)).length = 2 * ((d - 1) * d) :=
        programNumStab_hgpXZProgram d hd
      have h1 : (programMeasuresAt (hgpXZProgram d)).drop (2 * ((d - 1) * d)) = [] :=
        List.drop_eq_nil_of_le (le_of_eq hlen)
      have h2 : (List.finRange (2 * ((d - 1) * d))).drop (2 * ((d - 1) * d)) = [] :=
        List.drop_eq_nil_of_le (le_of_eq List.length_finRange)
      rw [h1, h2]
      simp only [List.flatMap_nil, runFScript]
      exact ⟨hR, (Nat.sub_self _).symm⟩
  | succ fuel ih =>
      intro k hfuel hk es hR
      have hklt : k < 2 * ((d - 1) * d) := by omega
      have hlen : (programMeasuresAt (hgpXZProgram d)).length = 2 * ((d - 1) * d) :=
        programNumStab_hgpXZProgram d hd
      have hklt' : k < (programMeasuresAt (hgpXZProgram d)).length := by
        rw [hlen]; exact hklt
      have hkltf : k < (List.finRange (2 * ((d - 1) * d))).length := by
        rw [List.length_finRange]; exact hklt
      have hdropms : (programMeasuresAt (hgpXZProgram d)).drop k
          = (programMeasuresAt (hgpXZProgram d))[k]
            :: (programMeasuresAt (hgpXZProgram d)).drop (k + 1) :=
        List.drop_eq_getElem_cons hklt'
      have hgetf : (List.finRange (2 * ((d - 1) * d)))[k]'hkltf = ⟨k, hklt⟩ := by
        apply Fin.ext
        simp [List.getElem_finRange]
      have hdropf : (List.finRange (2 * ((d - 1) * d))).drop k
          = (⟨k, hklt⟩ : Fin (2 * ((d - 1) * d)))
            :: (List.finRange (2 * ((d - 1) * d))).drop (k + 1) := by
        rw [List.drop_eq_getElem_cons hkltf, hgetf]
      have hscheme : (programMeasuresAt (hgpXZProgram d))[k].scheme = Scheme.NZ := by
        have h := congrArg (fun l => l[k]?) (hgpXZProgram_map_scheme d hd)
        simp only [List.getElem?_map, List.getElem?_eq_getElem hklt',
          List.getElem?_eq_getElem hkltf, Option.map_some] at h
        exact Option.some.injEq _ _ ▸ h
      have hsched : (programMeasuresAt (hgpXZProgram d))[k].schedule
          = hgpSchedule d hd ⟨k, hklt⟩ := by
        have h := congrArg (fun l => l[k]?) (hgpXZProgram_map_schedule d hd)
        simp only [List.getElem?_map, List.getElem?_eq_getElem hklt',
          List.getElem?_eq_getElem hkltf, Option.map_some, hgetf] at h
        exact Option.some.injEq _ _ ▸ h
      rw [hdropms, hdropf, List.flatMap_cons, List.flatMap_cons]
      rcases hmk : (programMeasuresAt (hgpXZProgram d))[k] with
        ⟨sch, sched, hstart, dstart, hfit, dfit⟩
      rw [hmk] at hscheme hsched
      simp only at hscheme hsched
      subst hscheme
      subst hsched
      rw [compileGadgetBlock_NZ_eq_nzBlock]
      set anc := blockHelperQ (d * d + (d - 1) * (d - 1))
        (programHelperCount (hgpXZProgram d)) hstart 1 hfit ⟨0, Nat.one_pos⟩ with hancdef
      have hanc : d * d + (d - 1) * (d - 1) ≤ anc.val := by
        simp only [hancdef, blockHelperQ]
        omega
      set slots := (liftSchedule (k := programHelperCount (hgpXZProgram d))
        (hgpSchedule d hd ⟨k, hklt⟩)).slots with hslots
      have hne : ∀ slot ∈ slots, slot.qubit ≠ anc :=
        lifted_slot_ne_anc _ anc hanc
      rw [runFScript_append]
      have hcnt : errLocCount (nzBlock anc slots)
          = (blockScript slots (hgpInjs d k)).length :=
        errLocCount_nzBlock anc slots (hgpInjs d k) hne
      have hhead : runFScript (nzBlock anc slots)
          (blockScript slots (hgpInjs d k)
            ++ ((List.finRange (2 * ((d - 1) * d))).drop (k + 1)).flatMap
              (fun j => blockScript (liftSchedule
                  (k := programHelperCount (hgpXZProgram d)) (hgpSchedule d hd j)).slots
                (hgpInjs d j.val))) es
          = runFScript (nzBlock anc slots) (blockScript slots (hgpInjs d k)) es :=
        runFScript_take_errLoc _ _ _ es (le_of_eq hcnt)
      have hdropscript : (blockScript slots (hgpInjs d k)
            ++ ((List.finRange (2 * ((d - 1) * d))).drop (k + 1)).flatMap
              (fun j => blockScript (liftSchedule
                  (k := programHelperCount (hgpXZProgram d)) (hgpSchedule d hd j)).slots
                (hgpInjs d j.val))).drop (errLocCount (nzBlock anc slots))
          = ((List.finRange (2 * ((d - 1) * d))).drop (k + 1)).flatMap
              (fun j => blockScript (liftSchedule
                  (k := programHelperCount (hgpXZProgram d)) (hgpSchedule d hd j)).slots
                (hgpInjs d j.val)) := by
        rw [hcnt]
        exact List.drop_left
      rw [hhead, hdropscript]
      obtain ⟨hR', hcount⟩ := hgp_reach_step d hd ⟨k, hklt⟩ anc hanc es hR
      have hcount' : (runFScript (nzBlock anc slots)
          (blockScript slots (hgpInjs d k)) es).2 = (if k < d then 1 else 0) := hcount
      have hR'' : ReachState (hgpRowB d (k + 1))
          (runFScript (nzBlock anc slots) (blockScript slots (hgpInjs d k)) es).1 := hR'
      obtain ⟨hRfin, hcntfin⟩ := ih (k + 1) (by omega) (by omega) _ hR''
      refine ⟨hRfin, ?_⟩
      rw [hcount', hcntfin]
      by_cases hkd : k < d
      · rw [if_pos hkd]
        omega
      · rw [if_neg hkd]
        omega

/-- **Full-circuit reach run**: from the clean state, the compiled HGP program
run on `hgpReachScript` leaves the row-0 `X̄` on the data block with every
detector quiet, firing exactly `d` faults. -/
theorem hgp_reach_run (d : Nat) (hd : 2 ≤ d) :
    ReachState (hgpRowB d (2 * ((d - 1) * d)))
        (runFScript (compileProgram (hgpXZProgram d)) (hgpReachScript d hd)
          (ErrorState.clean (d * d + (d - 1) * (d - 1)
            + programHelperCount (hgpXZProgram d)))).1
      ∧ (runFScript (compileProgram (hgpXZProgram d)) (hgpReachScript d hd)
          (ErrorState.clean (d * d + (d - 1) * (d - 1)
            + programHelperCount (hgpXZProgram d)))).2 = d := by
  have hprog : compileProgram (hgpXZProgram d)
      = (programMeasuresAt (hgpXZProgram d)).flatMap
          (fun m => compileGadgetBlock m.scheme m.schedule m.helperStart m.helperFit) :=
    compileProgramAux_eq_flatMap_programMeasuresAtAux 0 0 (hgpXZProgram d) _ _
  have hscript : hgpReachScript d hd
      = (List.finRange (2 * ((d - 1) * d))).flatMap
          (fun j => blockScript (liftSchedule
              (k := programHelperCount (hgpXZProgram d)) (hgpSchedule d hd j)).slots
            (hgpInjs d j.val)) := rfl
  have hclean : ReachState (hgpRowB d 0)
      (ErrorState.clean (d * d + (d - 1) * (d - 1)
        + programHelperCount (hgpXZProgram d))) := by
    refine ⟨fun q' => ?_, fun _ _ => rfl, fun _ => rfl⟩
    show Pauli.I = xOfBool (hgpRowB d 0 q')
    unfold hgpRowB
    rw [if_neg (by omega)]
    rfl
  have h0 := hgp_reach_fold d hd (2 * ((d - 1) * d)) 0 rfl (Nat.zero_le _) _ hclean
  rw [List.drop_zero, List.drop_zero] at h0
  rw [hprog, hscript]
  obtain ⟨hRf, hcnt⟩ := h0
  refine ⟨hRf, ?_⟩
  rw [hcnt]
  have hdd : d ≤ 2 * ((d - 1) * d) := by
    have h1 := Nat.le_mul_of_pos_left d (show 0 < d - 1 by omega)
    omega
  omega

/-! ## The discharged `reach` slot and `hgp_Safe` -/

/-- **The HGP `reach` VCSlot, discharged**: the row-0 script fires exactly
`d` faults and lands a genuine `failure` (the `X̄` residual, every flag
quiet). -/
theorem hgp_vcgen_reachD (d : Nat) (hd : 2 ≤ d)
    (hnq : 0 < d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d))
    (hnumStab : 0 < programNumStab (hgpXZProgram d)) :
    (vcgen (fullProgramVCInputD (hgpXZProgram d)
      (fullProgramReadoutDisjoint_auto (hgpXZProgram d)) d (by omega)
      hnq hnumStab)).denoteSlot .reach (hgpReachScript d hd) := by
  obtain ⟨hReach, hCount⟩ := hgp_reach_run d hd
  have hdd : d ≤ 2 * ((d - 1) * d) := by
    have h1 := Nat.le_mul_of_pos_left d (show 0 < d - 1 by omega)
    omega
  have hde : dataErrorOfQCState (hgpUParams d hd) (programHelperCount (hgpXZProgram d))
      (⟨(runFScript (compileProgram (hgpXZProgram d)) (hgpReachScript d hd)
          (ErrorState.clean _)).1, d⟩
        : QCState (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d)))
      = mkHGPRepLogicalX d hd := by
    funext q
    show (runFScript (compileProgram (hgpXZProgram d)) (hgpReachScript d hd)
        (ErrorState.clean _)).1.paulis
        (freshDataQ (d * d + (d - 1) * (d - 1))
          (programHelperCount (hgpXZProgram d)) q) = _
    rw [hReach.data q, xOfBool_hgpRowB]
    exact congrFun (hgpRowPref_total d (2 * ((d - 1) * d)) hd hdd) q
  refine ⟨hCount, ?_, allFlagsZero_of_detectors_false _ _ hReach.det⟩
  exact (hgpNZ_logicalFailure_iff d hd
    ⟨(runFScript (compileProgram (hgpXZProgram d)) (hgpReachScript d hd)
      (ErrorState.clean _)).1, d⟩).mpr
    ⟨fun j => by rw [hde]; exact hgp_Xbar_comm d hd j,
      by
        rw [hde]
        exact hgp_parityZ_not_InStab d hd (mkHGPRepLogicalX d hd)
          (by rw [ErrorVec.parity_symm]; exact hgp_Xbar_anticomm_Zbar d hd)⟩

/-- The canonical (generated-input) form. -/
theorem hgpXZ_vcgen_reachD (d : Nat) (hd : 2 ≤ d) :
    (vcgen (generatedFullProgramVCInputD (hgpXZProgram d) d (by omega)
      (hgp_nq_pos d hd) (hgp_numStab_pos d hd))).denoteSlot
      .reach (hgpReachScript d hd) :=
  hgp_vcgen_reachD d hd (hgp_nq_pos d hd) (hgp_numStab_pos d hd)

/-- **`hgp_Safe` — the paper's headline artifact.**  All five VCGen slots for
the compiled HGP program, discharged into the `DischargedVCs` record the
verifier's `vcgen_sound` consumes: `programEq`, `wf`, `syn`, `ftDistance`
(full coverage), and `reach` (the row-0 script) — for every `d ≥ 2`, with
`hd : 2 ≤ d` the only hypothesis. -/
def hgp_Safe (d : Nat) (hd : 2 ≤ d) :
    DischargedVCs (generatedFullProgramVCInputD (hgpXZProgram d) d
      (by omega) (hgp_nq_pos d hd) (hgp_numStab_pos d hd)) :=
  assembleDischargedVCs (hgpXZProgram d) d (by omega)
    (hgp_nq_pos d hd) (hgp_numStab_pos d hd)
    (hgpReachScript d hd)
    (hgpXZ_vcgen_ftDistanceD d hd)
    (hgpXZ_vcgen_reachD d hd)

/-- **The verifier's own soundness, applied**: the compiled HGP program is
`Safe` against its generated spec, for every `d ≥ 2` — a one-line instance of the
generic `assembleCodeSafe`. -/
theorem hgp_compiled_Safe (d : Nat) (hd : 2 ≤ d) :
    Safe (compileProgram (hgpXZProgram d))
      ((generatedFullProgramVCInputD (hgpXZProgram d) d (by omega)
        (hgp_nq_pos d hd) (hgp_numStab_pos d hd)).toCodeSpec) :=
  assembleCodeSafe (hgpXZProgram d) d (by omega)
    (hgp_nq_pos d hd) (hgp_numStab_pos d hd)
    (hgpReachScript d hd)
    (hgpXZ_vcgen_ftDistanceD d hd)
    (hgpXZ_vcgen_reachD d hd)

-- Regression guards (axiom pins) for the reach/Safe headliners.

/--
info: 'QStab.QClifford.Compile.hgp_reach_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgp_reach_step

/--
info: 'QStab.QClifford.Compile.hgp_reach_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgp_reach_run

/--
info: 'QStab.QClifford.Compile.hgp_vcgen_reachD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgp_vcgen_reachD

/--
info: 'QStab.QClifford.Compile.hgpXZ_vcgen_reachD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpXZ_vcgen_reachD

/--
info: 'QStab.QClifford.Compile.hgp_Safe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgp_Safe

/--
info: 'QStab.QClifford.Compile.hgp_compiled_Safe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgp_compiled_Safe

end QStab.QClifford.Compile
