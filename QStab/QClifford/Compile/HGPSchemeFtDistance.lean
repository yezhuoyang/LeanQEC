import QStab.QClifford.Compile.HGPNZFtDistance
import QStab.QClifford.Compile.HGPSchemeXDistance

/-!
# Compiled HGP `ftDistance` for every extraction scheme

`HGPNZFtDistance.lean` closes the NZ `ftDistance` slot from three ingredients:
the generic maximal-isotropic coverage (`hgp_coverage`), the two distance floors,
and the `logicalFailure`-iff `hgpNZ_logicalFailure_iff` (spec transport in
`HGPNZStabTransport.lean`).  Coverage and the class-landing lemmas
(`hgp_bar{X,Z}_contains_of`) are code-level, and both floors are now available for
every scheme (bar-Z via the framework, bar-X via `HGPSchemeXDistance.lean`).

The only NZ-specific piece was the spec transport.  But that transport is
program-generic underneath: the compiled program's *measured schedules* are the
scheme-independent `hgpSchedule` family (`hgpSchemeProgram scheme d` carries
`(scheme, hgpSchedule d hd i)` at each measurement leaf), and every downstream
faithfulness lemma (`scheduleRow_hgpSchedule_dataRestrict` / `_helperTrivial`,
`stabEntry_eq_I_of_not_mem`, `hgp_scheduleParity_eq_vectorParity`) is already
generic in the helper count `k`.  So the transport lifts over `scheme` by
swapping `hgpXZProgram d` → `hgpSchemeProgram scheme d` and generalizing the
schedule-alignment linchpin over the measurement tag.

Deliverables: `hgpScheme_ftDistance` and `hgpScheme_vcgen_ftDistanceD`, and the
`hgp{Shor,Knill,Flag}_ftDistance` / `_vcgen_ftDistanceD` instances, for every
`d ≥ 2`.  `reach` (hence `Safe`) is **not** addressed here — it remains NZ-only.
Everything routes through `hgpSchemeCircuit scheme d`
(`= compileProgram (hgpSchemeProgram scheme d)`); no re-defined circuit.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.Examples.HGPParametric
open QHL QHL.CodeHGPSchedule
open QHL.AssertionLang
open QHL.Source.Examples.HGP
open QHL.Source.Examples.HGPUnionSpec

/-! ## Schedule alignment for the scheme program -/

/-- **The measured schedules of a `foldr`-of-`seq`-`meas` program are the mapped
schedules — for any measurement tag `sch`.**  The tag-generalized twin of
`measuresAtAux_seqMeas_map_schedule` (the `.schedule` projection reads neither the
tag nor the offsets); same proof. -/
theorem measuresAtAux_seqMeas_map_schedule_gen {n th tf : Nat} {α : Type}
    (sch : Scheme) (g : α → RuleSchedule n) :
    ∀ (L : List α) (hs ds : Nat)
      (fit : hs + programHelperCount
        (L.foldr (fun a acc => XZProgram.seq (.meas sch (g a)) acc) XZProgram.skip) ≤ th)
      (dfit : ds + programDetectorCount
        (L.foldr (fun a acc => XZProgram.seq (.meas sch (g a)) acc) XZProgram.skip) ≤ tf),
      ((programMeasuresAtAux (totalHelpers := th) (totalFlags := tf) hs ds
        (L.foldr (fun a acc => XZProgram.seq (.meas sch (g a)) acc) XZProgram.skip)
        fit dfit).map (·.schedule)) = L.map g := by
  intro L
  induction L with
  | nil => intro hs ds fit dfit; rfl
  | cons a rest ih =>
      intro hs ds fit dfit
      simp only [List.foldr_cons, programMeasuresAtAux, List.map_cons, List.singleton_append]
      exact congrArg (g a :: ·) (ih _ _ _ _)

/-- The scheme program in `foldr`-of-`seq`-`meas` normal form (analog of
`hgpXZProgram_eq_foldr`, over the `scheme` tag). -/
theorem hgpSchemeProgram_eq_foldr (scheme : Scheme) (d : Nat) (hd : 2 ≤ d) :
    hgpSchemeProgram scheme d = (List.finRange (2 * ((d - 1) * d))).foldr
      (fun i acc => .seq (.meas scheme (hgpSchedule d hd i)) acc) .skip := by
  unfold hgpSchemeProgram xzProgramOfProgramsWith
  rw [show (List.range (2 * ((d - 1) * d)))
        = (List.finRange (2 * ((d - 1) * d))).map Fin.val from by
      apply List.ext_getElem
      · simp
      · intro j h1 h2; simp,
    List.foldr_map]
  congr 1
  funext i acc
  rw [genSchedule_eq_hgpSchedule d hd i]

/-- The measured schedules of `hgpSchemeProgram scheme d` are the `hgpSchedule`
family — scheme-independent. -/
theorem hgpSchemeProgram_map_schedule (scheme : Scheme) (d : Nat) (hd : 2 ≤ d) :
    (programMeasuresAt (hgpSchemeProgram scheme d)).map (·.schedule) =
      (List.finRange (2 * ((d - 1) * d))).map (hgpSchedule d hd) := by
  rw [hgpSchemeProgram_eq_foldr scheme d hd]
  unfold programMeasuresAt
  exact measuresAtAux_seqMeas_map_schedule_gen scheme (hgpSchedule d hd)
    (List.finRange (2 * ((d - 1) * d))) 0 0 _ _

/-- The scheme program measures exactly `2·(d−1)·d` generators. -/
theorem programNumStab_hgpSchemeProgram (scheme : Scheme) (d : Nat) (hd : 2 ≤ d) :
    programNumStab (hgpSchemeProgram scheme d) = 2 * ((d - 1) * d) := by
  unfold programNumStab
  have hl := congrArg List.length (hgpSchemeProgram_map_schedule scheme d hd)
  simpa using hl

/-- Schedule-at-`i` alignment for the scheme program. -/
theorem hgpSchemeProgram_schedule_get (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (i : Fin (programNumStab (hgpSchemeProgram scheme d))) :
    ((programMeasuresAt (hgpSchemeProgram scheme d)).get i).schedule =
      hgpSchedule d hd (Fin.cast (programNumStab_hgpSchemeProgram scheme d hd) i) := by
  have h := hgpSchemeProgram_map_schedule scheme d hd
  have hi2 : i.val < 2 * ((d - 1) * d) := by
    rw [← programNumStab_hgpSchemeProgram scheme d hd]; exact i.isLt
  have key : ((programMeasuresAt (hgpSchemeProgram scheme d)).map (·.schedule))[i.val]?
      = ((List.finRange (2 * ((d - 1) * d))).map (hgpSchedule d hd))[i.val]? := by rw [h]
  rw [List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem
      (show i.val < (programMeasuresAt (hgpSchemeProgram scheme d)).length from i.isLt),
    List.getElem?_eq_getElem (by rw [List.length_finRange]; exact hi2)] at key
  simp only [Option.map_some, Option.some.injEq, List.getElem_finRange] at key
  rw [List.get_eq_getElem, key]
  congr 1

/-! ## The scheme spec and its transports -/

/-- The compiled HGP PCC spec of the scheme program at distance `d`. -/
def hgpSchemeSpec (scheme : Scheme) (d : Nat) (hd : 2 ≤ d) :
    CodeSpec (d * d + (d - 1) * (d - 1) + programHelperCount (hgpSchemeProgram scheme d)) :=
  fullProgramCodeSpecD (hgpSchemeProgram scheme d)
    (fullProgramReadoutDisjoint_auto (hgpSchemeProgram scheme d)) d (by omega)

/-- Source-side data residual of an ambient error state of the scheme circuit. -/
def hgpSchemeDataError (scheme : Scheme) (d : Nat)
    (es : ErrorState (d * d + (d - 1) * (d - 1) + programHelperCount (hgpSchemeProgram scheme d))) :
    ErrorVec (d * d + (d - 1) * (d - 1)) :=
  fun q' => es.paulis
    (freshDataQ (d * d + (d - 1) * (d - 1)) (programHelperCount (hgpSchemeProgram scheme d)) q')

/-- The single canonical index equality for the scheme spec. -/
theorem hgpSchemeNumStab_eq (scheme : Scheme) (d : Nat) (hd : 2 ≤ d) :
    (hgpSchemeSpec scheme d hd).numStab = (hgpUParams d hd).numStab :=
  programNumStab_hgpSchemeProgram scheme d hd

/-- The compiled `i`-th stabilizer of the scheme spec, read on a data qubit, is
the source generator `(cast i)`. -/
theorem hgpScheme_spec_stab_data (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (i : Fin (hgpSchemeSpec scheme d hd).numStab) (q' : Fin (d * d + (d - 1) * (d - 1))) :
    (hgpSchemeSpec scheme d hd).stabilizer i
        (freshDataQ (d * d + (d - 1) * (d - 1))
          (programHelperCount (hgpSchemeProgram scheme d)) q') =
      (hgpUParams d hd).stabilizers (Fin.cast (hgpSchemeNumStab_eq scheme d hd) i) q' := by
  show scheduleRow (k := programHelperCount (hgpSchemeProgram scheme d))
        ((programMeasuresAt (hgpSchemeProgram scheme d)).get i).schedule
        (freshDataQ (d * d + (d - 1) * (d - 1))
          (programHelperCount (hgpSchemeProgram scheme d)) q') = _
  rw [hgpSchemeProgram_schedule_get scheme d hd i,
    scheduleRow_hgpSchedule_dataRestrict d hd _ _ q']
  rfl

/-- The compiled `i`-th stabilizer of the scheme spec is `I` on every helper. -/
theorem hgpScheme_spec_stab_helper (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (i : Fin (hgpSchemeSpec scheme d hd).numStab)
    (q : Fin (d * d + (d - 1) * (d - 1) + programHelperCount (hgpSchemeProgram scheme d)))
    (hq : d * d + (d - 1) * (d - 1) ≤ q.val) :
    (hgpSchemeSpec scheme d hd).stabilizer i q = Pauli.I := by
  show scheduleRow (k := programHelperCount (hgpSchemeProgram scheme d))
        ((programMeasuresAt (hgpSchemeProgram scheme d)).get i).schedule q = _
  rw [hgpSchemeProgram_schedule_get scheme d hd i]
  exact scheduleRow_hgpSchedule_helperTrivial d hd _ _ q hq

/-- Value transport on data qubits (scheme spec). -/
theorem hgpScheme_prodStab_data (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (mask : Fin (hgpSchemeSpec scheme d hd).numStab → Bool)
    (q' : Fin (d * d + (d - 1) * (d - 1))) :
    prodStab (hgpSchemeSpec scheme d hd) mask
        (freshDataQ (d * d + (d - 1) * (d - 1))
          (programHelperCount (hgpSchemeProgram scheme d)) q') =
      qecMaskProd (hgpUParams d hd)
        (fun i' => mask (Fin.cast (hgpSchemeNumStab_eq scheme d hd).symm i')) q' := by
  unfold prodStab
  rw [qecMaskProd_apply]
  exact foldl_transport (hgpSchemeNumStab_eq scheme d hd) mask
    (fun i => (hgpSchemeSpec scheme d hd).stabilizer i
      (freshDataQ (d * d + (d - 1) * (d - 1))
        (programHelperCount (hgpSchemeProgram scheme d)) q'))
    (fun i' => (hgpUParams d hd).stabilizers i' q')
    (fun i => hgpScheme_spec_stab_data scheme d hd i q') Pauli.I

/-- Value transport on helper qubits (scheme spec). -/
theorem hgpScheme_prodStab_helper (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (mask : Fin (hgpSchemeSpec scheme d hd).numStab → Bool)
    (q : Fin (d * d + (d - 1) * (d - 1) + programHelperCount (hgpSchemeProgram scheme d)))
    (hq : d * d + (d - 1) * (d - 1) ≤ q.val) :
    prodStab (hgpSchemeSpec scheme d hd) mask q = Pauli.I := by
  unfold prodStab
  exact foldl_pauliMul_allI mask (fun i => (hgpSchemeSpec scheme d hd).stabilizer i q)
    (List.finRange _) (fun i _ => hgpScheme_spec_stab_helper scheme d hd i q hq) Pauli.I

/-! ## The headline transports -/

/-- **Stab-half over the raw error state** (scheme spec). -/
theorem hgpScheme_Stab_iff_InStab_es (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (es : ErrorState (d * d + (d - 1) * (d - 1)
      + programHelperCount (hgpSchemeProgram scheme d))) :
    Stab (hgpSchemeSpec scheme d hd) (dataVector (hgpSchemeSpec scheme d hd) es) ↔
      InStab (hgpUParams d hd) (hgpSchemeDataError scheme d es) := by
  rw [InStab_iff_qecMaskProd]
  constructor
  · rintro ⟨mask, hmask⟩
    refine ⟨fun i' => mask (Fin.cast (hgpSchemeNumStab_eq scheme d hd).symm i'), ?_⟩
    funext q'
    have hq0 := hmask (freshDataQ (d * d + (d - 1) * (d - 1))
      (programHelperCount (hgpSchemeProgram scheme d)) q')
    rw [hgpScheme_prodStab_data scheme d hd mask q'] at hq0
    rw [← hq0]
    show es.paulis (freshDataQ (d * d + (d - 1) * (d - 1))
        (programHelperCount (hgpSchemeProgram scheme d)) q')
      = (if (hgpSchemeSpec scheme d hd).isData
            (freshDataQ (d * d + (d - 1) * (d - 1))
              (programHelperCount (hgpSchemeProgram scheme d)) q')
          then es.paulis (freshDataQ (d * d + (d - 1) * (d - 1))
            (programHelperCount (hgpSchemeProgram scheme d)) q')
          else Pauli.I)
    rw [if_pos (by
      show decide ((freshDataQ (d * d + (d - 1) * (d - 1))
          (programHelperCount (hgpSchemeProgram scheme d)) q').val
          < d * d + (d - 1) * (d - 1)) = true
      rw [freshDataQ_val]
      exact decide_eq_true q'.isLt)]
  · rintro ⟨mask', hmask'⟩
    refine ⟨fun i => mask' (Fin.cast (hgpSchemeNumStab_eq scheme d hd) i), ?_⟩
    intro q
    by_cases hq : q.val < d * d + (d - 1) * (d - 1)
    · have hqeq : q = freshDataQ (d * d + (d - 1) * (d - 1))
          (programHelperCount (hgpSchemeProgram scheme d)) ⟨q.val, hq⟩ :=
        Fin.ext (by rw [freshDataQ_val])
      rw [hqeq, hgpScheme_prodStab_data scheme d hd
        (fun i => mask' (Fin.cast (hgpSchemeNumStab_eq scheme d hd) i)) ⟨q.val, hq⟩]
      show (if (hgpSchemeSpec scheme d hd).isData
              (freshDataQ (d * d + (d - 1) * (d - 1))
                (programHelperCount (hgpSchemeProgram scheme d)) ⟨q.val, hq⟩)
            then es.paulis (freshDataQ (d * d + (d - 1) * (d - 1))
              (programHelperCount (hgpSchemeProgram scheme d)) ⟨q.val, hq⟩)
            else Pauli.I) = _
      rw [if_pos (by
        show decide ((freshDataQ (d * d + (d - 1) * (d - 1))
            (programHelperCount (hgpSchemeProgram scheme d)) ⟨q.val, hq⟩).val
            < d * d + (d - 1) * (d - 1)) = true
        rw [freshDataQ_val]
        exact decide_eq_true hq)]
      have hcast : (fun i' => mask' (Fin.cast (hgpSchemeNumStab_eq scheme d hd)
          (Fin.cast (hgpSchemeNumStab_eq scheme d hd).symm i'))) = mask' := by
        funext i'
        exact congrArg mask' (Fin.ext rfl)
      rw [hcast]
      exact congrFun hmask' ⟨q.val, hq⟩
    · have hq' : d * d + (d - 1) * (d - 1) ≤ q.val := Nat.le_of_not_lt hq
      rw [hgpScheme_prodStab_helper scheme d hd
        (fun i => mask' (Fin.cast (hgpSchemeNumStab_eq scheme d hd) i)) q hq']
      show (if (hgpSchemeSpec scheme d hd).isData q then es.paulis q else Pauli.I) = Pauli.I
      rw [if_neg (by
        show ¬ (decide (q.val < d * d + (d - 1) * (d - 1)) = true)
        rw [decide_eq_true_eq]
        exact hq)]

/-- **Centralizer-half over the raw error state** (scheme spec). -/
theorem hgpScheme_centralizer_iff_es (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (es : ErrorState (d * d + (d - 1) * (d - 1)
      + programHelperCount (hgpSchemeProgram scheme d))) :
    Centralizer (hgpSchemeSpec scheme d hd) (dataVector (hgpSchemeSpec scheme d hd) es) ↔
      ∀ j : Fin (hgpUParams d hd).numStab,
        ErrorVec.parity ((hgpUParams d hd).stabilizers j)
          (hgpSchemeDataError scheme d es) = false := by
  refine Iff.trans (compiled_centralizer_transport (hgpSchemeProgram scheme d)
    (fullProgramReadoutDisjoint_auto (hgpSchemeProgram scheme d)) d (by omega) es) ?_
  show (∀ i : Fin (programNumStab (hgpSchemeProgram scheme d)),
      scheduleParity ((programMeasuresAt (hgpSchemeProgram scheme d)).get i).schedule
        (hgpSchemeDataError scheme d es) = false) ↔ _
  have hbridge : ∀ i : Fin (programNumStab (hgpSchemeProgram scheme d)),
      scheduleParity ((programMeasuresAt (hgpSchemeProgram scheme d)).get i).schedule
          (hgpSchemeDataError scheme d es)
        = ErrorVec.parity ((hgpUParams d hd).stabilizers
            (Fin.cast (hgpSchemeNumStab_eq scheme d hd) i)) (hgpSchemeDataError scheme d es) := by
    intro i
    rw [hgpSchemeProgram_schedule_get scheme d hd i,
      hgp_scheduleParity_eq_vectorParity d hd _ (hgpSchemeDataError scheme d es),
      vectorParity_eq_parity]
    rfl
  simp only [hbridge]
  exact Fin_cast_forall_iff (hgpSchemeNumStab_eq scheme d hd)
    (fun j => ErrorVec.parity ((hgpUParams d hd).stabilizers j)
      (hgpSchemeDataError scheme d es) = false)

/-- **The scheme `logicalFailure` iff**: the compiled scheme spec's
`logicalFailure` is the source-side `(centralizer ∧ ¬ InStab)` on the data
residual. -/
theorem hgpScheme_logicalFailure_iff (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (sigma : QCState (d * d + (d - 1) * (d - 1)
      + programHelperCount (hgpSchemeProgram scheme d))) :
    QStab.QClifford.PCC.logicalFailure (hgpSchemeSpec scheme d hd) sigma.es ↔
      ((∀ j : Fin (hgpUParams d hd).numStab,
          ErrorVec.parity ((hgpUParams d hd).stabilizers j)
            (dataErrorOfQCState (hgpUParams d hd)
              (programHelperCount (hgpSchemeProgram scheme d)) sigma) = false)
        ∧ ¬ InStab (hgpUParams d hd)
            (dataErrorOfQCState (hgpUParams d hd)
              (programHelperCount (hgpSchemeProgram scheme d)) sigma)) := by
  show QStab.QClifford.PCC.logicalFailure (hgpSchemeSpec scheme d hd) sigma.es ↔
    ((∀ j : Fin (hgpUParams d hd).numStab,
        ErrorVec.parity ((hgpUParams d hd).stabilizers j)
          (hgpSchemeDataError scheme d sigma.es) = false)
      ∧ ¬ InStab (hgpUParams d hd) (hgpSchemeDataError scheme d sigma.es))
  unfold QStab.QClifford.PCC.logicalFailure
  exact and_congr (hgpScheme_centralizer_iff_es scheme d hd sigma.es)
    (not_congr (hgpScheme_Stab_iff_InStab_es scheme d hd sigma.es))

/-! ## The scheme `ftDistance` and its VCGen slot -/

/-- **Compiled HGP `ftDistance` for any extraction scheme**, given its
`HGPSchemeHValid` witness: every clean-start run of `hgpSchemeCircuit scheme d`
whose error state is a `logicalFailure` fired at least `d` faults — full
coverage, for every `d ≥ 2`. -/
theorem hgpScheme_ftDistance (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (hv : HGPSchemeHValid scheme d hd)
    (sigma : QCState (d * d + (d - 1) * (d - 1)
      + programHelperCount (hgpSchemeProgram scheme d)))
    (hrun : qceval (hgpSchemeCircuit scheme d)
      (QCState.clean (d * d + (d - 1) * (d - 1)
        + programHelperCount (hgpSchemeProgram scheme d))) sigma)
    (hfail : QStab.QClifford.PCC.logicalFailure (hgpSchemeSpec scheme d hd) sigma.es) :
    d ≤ sigma.lambda := by
  rw [hgpScheme_logicalFailure_iff scheme d hd sigma] at hfail
  obtain ⟨hcent, hnot⟩ := hfail
  rcases hgp_coverage d hd _ hcent hnot with hx | hz
  · exact hgpScheme_compiled_barX_distance scheme d hd hv sigma hrun
      (hgp_barX_contains_of d hd _ hcent hx)
  · exact hgpScheme_compiled_barZ_distance scheme d hd hv sigma hrun
      (hgp_barZ_contains_of d hd _ hcent hz)

/-- **The discharged VCGen `ftDistance` slot** for the compiled scheme program. -/
theorem hgpScheme_vcgen_ftDistanceD (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (hv : HGPSchemeHValid scheme d hd)
    (hnq : 0 < d * d + (d - 1) * (d - 1) + programHelperCount (hgpSchemeProgram scheme d))
    (hnumStab : 0 < programNumStab (hgpSchemeProgram scheme d)) :
    (vcgen (fullProgramVCInputD (hgpSchemeProgram scheme d)
      (fullProgramReadoutDisjoint_auto (hgpSchemeProgram scheme d)) d (by omega)
      hnq hnumStab)).denoteSlot .ftDistance := by
  intro sigma hrun _hflags
  rw [denoteQC_circuitDistanceAny]
  intro hfail
  exact hgpScheme_ftDistance scheme d hd hv sigma hrun hfail

theorem hgpScheme_nq_pos (scheme : Scheme) (d : Nat) (hd : 2 ≤ d) :
    0 < d * d + (d - 1) * (d - 1) + programHelperCount (hgpSchemeProgram scheme d) := by
  have h1 : 0 < d * d := Nat.mul_pos (by omega) (by omega)
  omega

theorem hgpScheme_numStab_pos (scheme : Scheme) (d : Nat) (hd : 2 ≤ d) :
    0 < programNumStab (hgpSchemeProgram scheme d) := by
  rw [programNumStab_hgpSchemeProgram scheme d hd]
  have h1 : 0 < (d - 1) * d := Nat.mul_pos (by omega) (by omega)
  omega

/-- **The canonical scheme `ftDistance` VCGen slot**, side conditions internal. -/
theorem hgpScheme_vcgen_ftDistanceD_canonical (scheme : Scheme) (d : Nat) (hd : 2 ≤ d)
    (hv : HGPSchemeHValid scheme d hd) :
    (vcgen (generatedFullProgramVCInputD (hgpSchemeProgram scheme d) d (by omega)
      (hgpScheme_nq_pos scheme d hd) (hgpScheme_numStab_pos scheme d hd))).denoteSlot
      .ftDistance :=
  hgpScheme_vcgen_ftDistanceD scheme d hd hv
    (hgpScheme_nq_pos scheme d hd) (hgpScheme_numStab_pos scheme d hd)

/-! ## The three scheme-specific `ftDistance` instances -/

/-- **Compiled HGP `ftDistance` under Shor extraction.** -/
theorem hgpShor_ftDistance (d : Nat) (hd : 2 ≤ d)
    (sigma : QCState (d * d + (d - 1) * (d - 1)
      + programHelperCount (hgpSchemeProgram Scheme.Shor d)))
    (hrun : qceval (hgpSchemeCircuit Scheme.Shor d)
      (QCState.clean (d * d + (d - 1) * (d - 1)
        + programHelperCount (hgpSchemeProgram Scheme.Shor d))) sigma)
    (hfail : QStab.QClifford.PCC.logicalFailure (hgpSchemeSpec Scheme.Shor d hd) sigma.es) :
    d ≤ sigma.lambda :=
  hgpScheme_ftDistance Scheme.Shor d hd
    (hgpScheme_hvalid Scheme.Shor d hd (hgpShor_leafClean d hd) shor_SchemeClassifier)
    sigma hrun hfail

/-- **Compiled HGP `ftDistance` under Knill extraction.** -/
theorem hgpKnill_ftDistance (d : Nat) (hd : 2 ≤ d)
    (sigma : QCState (d * d + (d - 1) * (d - 1)
      + programHelperCount (hgpSchemeProgram Scheme.Knill d)))
    (hrun : qceval (hgpSchemeCircuit Scheme.Knill d)
      (QCState.clean (d * d + (d - 1) * (d - 1)
        + programHelperCount (hgpSchemeProgram Scheme.Knill d))) sigma)
    (hfail : QStab.QClifford.PCC.logicalFailure (hgpSchemeSpec Scheme.Knill d hd) sigma.es) :
    d ≤ sigma.lambda :=
  hgpScheme_ftDistance Scheme.Knill d hd
    (hgpScheme_hvalid Scheme.Knill d hd (hgpKnill_leafClean d hd) knill_SchemeClassifier)
    sigma hrun hfail

/-- **Compiled HGP `ftDistance` under Flag extraction.** -/
theorem hgpFlag_ftDistance (d : Nat) (hd : 2 ≤ d)
    (sigma : QCState (d * d + (d - 1) * (d - 1)
      + programHelperCount (hgpSchemeProgram Scheme.Flag d)))
    (hrun : qceval (hgpSchemeCircuit Scheme.Flag d)
      (QCState.clean (d * d + (d - 1) * (d - 1)
        + programHelperCount (hgpSchemeProgram Scheme.Flag d))) sigma)
    (hfail : QStab.QClifford.PCC.logicalFailure (hgpSchemeSpec Scheme.Flag d hd) sigma.es) :
    d ≤ sigma.lambda :=
  hgpScheme_ftDistance Scheme.Flag d hd
    (hgpScheme_hvalid Scheme.Flag d hd (hgpFlag_leafClean d hd) flag_SchemeClassifier)
    sigma hrun hfail

/-- **VCGen `ftDistance` slots** for the three schemes. -/
theorem hgpShor_vcgen_ftDistanceD (d : Nat) (hd : 2 ≤ d) :
    (vcgen (generatedFullProgramVCInputD (hgpSchemeProgram Scheme.Shor d) d (by omega)
      (hgpScheme_nq_pos Scheme.Shor d hd) (hgpScheme_numStab_pos Scheme.Shor d hd))).denoteSlot
      .ftDistance :=
  hgpScheme_vcgen_ftDistanceD_canonical Scheme.Shor d hd
    (hgpScheme_hvalid Scheme.Shor d hd (hgpShor_leafClean d hd) shor_SchemeClassifier)

theorem hgpKnill_vcgen_ftDistanceD (d : Nat) (hd : 2 ≤ d) :
    (vcgen (generatedFullProgramVCInputD (hgpSchemeProgram Scheme.Knill d) d (by omega)
      (hgpScheme_nq_pos Scheme.Knill d hd) (hgpScheme_numStab_pos Scheme.Knill d hd))).denoteSlot
      .ftDistance :=
  hgpScheme_vcgen_ftDistanceD_canonical Scheme.Knill d hd
    (hgpScheme_hvalid Scheme.Knill d hd (hgpKnill_leafClean d hd) knill_SchemeClassifier)

theorem hgpFlag_vcgen_ftDistanceD (d : Nat) (hd : 2 ≤ d) :
    (vcgen (generatedFullProgramVCInputD (hgpSchemeProgram Scheme.Flag d) d (by omega)
      (hgpScheme_nq_pos Scheme.Flag d hd) (hgpScheme_numStab_pos Scheme.Flag d hd))).denoteSlot
      .ftDistance :=
  hgpScheme_vcgen_ftDistanceD_canonical Scheme.Flag d hd
    (hgpScheme_hvalid Scheme.Flag d hd (hgpFlag_leafClean d hd) flag_SchemeClassifier)

/-! ## Regression guards (axiom pins) -/

/--
info: 'QStab.QClifford.Compile.hgpScheme_logicalFailure_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpScheme_logicalFailure_iff

/--
info: 'QStab.QClifford.Compile.hgpScheme_ftDistance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpScheme_ftDistance

/--
info: 'QStab.QClifford.Compile.hgpShor_vcgen_ftDistanceD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpShor_vcgen_ftDistanceD

/--
info: 'QStab.QClifford.Compile.hgpKnill_vcgen_ftDistanceD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpKnill_vcgen_ftDistanceD

/--
info: 'QStab.QClifford.Compile.hgpFlag_vcgen_ftDistanceD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpFlag_vcgen_ftDistanceD

end QStab.QClifford.Compile
