import QStab.QClifford.Compile.StabTransportCore
import QStab.QClifford.Compile.SurfaceNZSpecAlign
import QStab.QClifford.Compile.HGPHValid

/-!
# HGP F1: the dimensional transport `Stab (compiled) ↔ InStab (source)`

The HGP instance of the surface transport (`SurfaceNZStabTransport`), built on
the **public** generic engine (`StabTransportCore`):

* support completeness (`stabEntry_eq_I_of_not_mem`) — the converse of
  `stabEntry_mem_supportList`, closing the schedule-row faithfulness;
* the schedule alignment (`hgpXZProgram_schedule_get`) via the generic
  `measuresAtAux_seqMeas_map_schedule` on the landed `hgpXZProgram_eq_foldr`;
* the faithfulness legs (`scheduleRow_hgpSchedule_dataRestrict` /
  `_helperTrivial`) via the generic `scheduleRow_eval_uniform`;
* the assembled transports `hgpNZ_Stab_iff_InStab` and
  `hgpNZ_logicalFailure_iff` over
  `fullProgramCodeSpecD (hgpXZProgram d)`.

Unlike the surface file, the raw-`ErrorState` aux forms (`_es`) are **public**
— the surface's private auxes were a confirmed reuse obstacle.
Everything is decide-free and parametric in `d ≥ 2`.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.Examples.HGPParametric
open QHL QHL.CodeHGPSchedule
open QHL.Source.Examples.HGPUnionSpec

/-! ## Support completeness -/

/-- **Support completeness**: off the pinned support list, the generator entry
is `I` — the converse of `stabEntry_mem_supportList`. -/
theorem stabEntry_eq_I_of_not_mem (d k q : Nat) (hd : 2 ≤ d)
    (hk : k < 2 * ((d - 1) * d)) (hqlt : q < d * d + (d - 1) * (d - 1))
    (hq : q ∉ hgpSupportList d k) :
    QStab.Examples.HGPParametric.stabEntry d k q = Pauli.I := by
  have hd0 : 0 < d := by omega
  have hd1 : 0 < d - 1 := by omega
  by_cases hx : k < (d - 1) * d
  · -- X check
    by_cases hqd : q < d * d
    · rw [stabEntry_X_s1_eq d k q hx hqd, if_neg ?_]
      intro ⟨hmod, hdiv⟩
      have hdm := Nat.div_add_mod q d
      apply hq
      unfold hgpSupportList
      rw [if_pos hx]
      rcases hdiv with hdiv | hdiv
      · have hqe : q = d * (k / d) + k % d := by
          rw [← hdiv, ← hmod]; omega
        rw [hqe]
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
          (List.mem_cons.mpr (Or.inl rfl)))))
      · have hqe : q = d * (k / d + 1) + k % d := by
          rw [← hdiv, ← hmod]; omega
        rw [hqe]
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
          (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))
    · rw [stabEntry_X_s2_eq d k q hx hqd hqlt, if_neg ?_]
      intro ⟨hdiv, hmod⟩
      have hple : d * d ≤ q := Nat.le_of_not_lt hqd
      have hdm := Nat.div_add_mod (q - d * d) (d - 1)
      rw [hdiv] at hdm
      have hmlt : (q - d * d) % (d - 1) < d - 1 := Nat.mod_lt _ hd1
      apply hq
      unfold hgpSupportList
      rw [if_pos hx]
      rcases hmod with hmod | hmod
      · -- B entry, guard `k % d ≤ d - 2`
        have hguard : k % d ≤ d - 2 := by omega
        have hqe : q = d * d + k / d * (d - 1) + k % d := by
          rw [Nat.mul_comm (k / d) (d - 1)]
          omega
        rw [if_pos hguard, hqe]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      · -- A entry, guard `1 ≤ k % d`
        have hguard : 1 ≤ k % d := by omega
        have hqe : q = d * d + k / d * (d - 1) + (k % d - 1) := by
          rw [Nat.mul_comm (k / d) (d - 1)]
          omega
        rw [if_pos hguard, hqe]
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
          (List.mem_cons.mpr (Or.inl rfl)))))
  · -- Z check
    have hzk : (d - 1) * d ≤ k := Nat.le_of_not_lt hx
    by_cases hqd : q < d * d
    · rw [stabEntry_Z_s1_eq d k q hzk hk hqd, if_neg ?_]
      intro ⟨hdiv, hmod⟩
      have hdm := Nat.div_add_mod q d
      apply hq
      unfold hgpSupportList
      rw [if_neg hx]
      rcases hmod with hmod | hmod
      · have hqe : q = d * ((k - (d - 1) * d) / (d - 1))
            + (k - (d - 1) * d) % (d - 1) := by
          rw [← hdiv, ← hmod]; omega
        rw [hqe]
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
          (List.mem_cons.mpr (Or.inl rfl)))))
      · have hqe : q = d * ((k - (d - 1) * d) / (d - 1))
            + ((k - (d - 1) * d) % (d - 1) + 1) := by
          rw [← hdiv, ← hmod]; omega
        rw [hqe]
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
          (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))
    · rw [stabEntry_Z_s2_eq d k q hzk hk hqd hqlt, if_neg ?_]
      intro ⟨hmod, hdiv⟩
      have hple : d * d ≤ q := Nat.le_of_not_lt hqd
      have hsub : q - d * d + d * d = q := Nat.sub_add_cancel hple
      have hplt : q - d * d < (d - 1) * (d - 1) := by omega
      have hdlt : (q - d * d) / (d - 1) < d - 1 :=
        (Nat.div_lt_iff_lt_mul hd1).mpr hplt
      have hdm := Nat.div_add_mod (q - d * d) (d - 1)
      rw [hmod] at hdm
      apply hq
      unfold hgpSupportList
      rw [if_neg hx]
      rcases hdiv with hdiv | hdiv
      · -- B entry, guard `(k - (d-1)*d) / (d-1) ≤ d - 2`
        have h1 : (k - (d - 1) * d) / (d - 1) < d - 1 := hdiv ▸ hdlt
        have hguard : (k - (d - 1) * d) / (d - 1) ≤ d - 2 :=
          Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le h1 (by omega))
        have hqe : q = d * d + (k - (d - 1) * d) / (d - 1) * (d - 1)
            + (k - (d - 1) * d) % (d - 1) := by
          rw [Nat.mul_comm ((k - (d - 1) * d) / (d - 1)) (d - 1), ← hdiv,
            Nat.add_assoc, hdm, Nat.add_comm (d * d) (q - d * d), hsub]
        rw [if_pos hguard, hqe]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      · -- A entry, guard `1 ≤ (k - (d-1)*d) / (d-1)`
        have hguard : 1 ≤ (k - (d - 1) * d) / (d - 1) := by
          rw [← hdiv]
          simp
        have hstep : (k - (d - 1) * d) / (d - 1) - 1 = (q - d * d) / (d - 1) := by
          rw [← hdiv]
          simp
        have hqe : q = d * d + ((k - (d - 1) * d) / (d - 1) - 1) * (d - 1)
            + (k - (d - 1) * d) % (d - 1) := by
          rw [Nat.mul_comm ((k - (d - 1) * d) / (d - 1) - 1) (d - 1), hstep,
            Nat.add_assoc, hdm, Nat.add_comm (d * d) (q - d * d), hsub]
        rw [if_pos hguard, hqe]
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
          (List.mem_cons.mpr (Or.inl rfl)))))

/-! ## Schedule alignment (the linchpin, via the generic fold lemma) -/

/-- The measured schedules of `hgpXZProgram` are the `hgpSchedule` family. -/
theorem hgpXZProgram_map_schedule (d : Nat) (hd : 2 ≤ d) :
    (programMeasuresAt (hgpXZProgram d)).map (·.schedule) =
      (List.finRange (2 * ((d - 1) * d))).map (hgpSchedule d hd) := by
  rw [hgpXZProgram_eq_foldr d hd]
  unfold programMeasuresAt
  exact measuresAtAux_seqMeas_map_schedule (hgpSchedule d hd)
    (List.finRange (2 * ((d - 1) * d))) 0 0 _ _

/-- **Stabilizer count:** the compiled HGP program measures exactly
`2·(d−1)·d` generators. -/
theorem programNumStab_hgpXZProgram (d : Nat) (hd : 2 ≤ d) :
    programNumStab (hgpXZProgram d) = 2 * ((d - 1) * d) := by
  unfold programNumStab
  have hl := congrArg List.length (hgpXZProgram_map_schedule d hd)
  simpa using hl

/-- **Schedule-at-`i` alignment:** the `i`-th measured schedule of the
compiled HGP program is `hgpSchedule d hd i` (index cast along
`programNumStab_hgpXZProgram`). -/
theorem hgpXZProgram_schedule_get (d : Nat) (hd : 2 ≤ d)
    (i : Fin (programNumStab (hgpXZProgram d))) :
    ((programMeasuresAt (hgpXZProgram d)).get i).schedule =
      hgpSchedule d hd (Fin.cast (programNumStab_hgpXZProgram d hd) i) := by
  have h := hgpXZProgram_map_schedule d hd
  have hi2 : i.val < 2 * ((d - 1) * d) := by
    rw [← programNumStab_hgpXZProgram d hd]; exact i.isLt
  have key : ((programMeasuresAt (hgpXZProgram d)).map (·.schedule))[i.val]?
      = ((List.finRange (2 * ((d - 1) * d))).map (hgpSchedule d hd))[i.val]? := by rw [h]
  rw [List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem
      (show i.val < (programMeasuresAt (hgpXZProgram d)).length from i.isLt),
    List.getElem?_eq_getElem (by rw [List.length_finRange]; exact hi2)] at key
  simp only [Option.map_some, Option.some.injEq, List.getElem_finRange] at key
  rw [List.get_eq_getElem, key]
  congr 1

/-! ## Schedule-row faithfulness -/

private theorem hgpSchedule_slots_qubits (d : Nat) (hd : 2 ≤ d)
    (i : Fin (2 * ((d - 1) * d))) :
    (hgpSchedule d hd i).slots.map (·.qubit)
      = (hgpSupportList d i.val).map (hgpFin d hd) := by
  unfold hgpSchedule RuleSchedule.uniform
  simp [List.map_map, Function.comp]

/-- **Faithfulness on data qubits.**  The compiled `i`-th stabilizer row,
restricted to the data block, is exactly `mkHGPRepStabilizers d i`. -/
theorem scheduleRow_hgpSchedule_dataRestrict (d : Nat) (hd : 2 ≤ d)
    (i : Fin (2 * ((d - 1) * d))) (k : Nat) (q : Fin (d * d + (d - 1) * (d - 1))) :
    scheduleRow (k := k) (hgpSchedule d hd i)
        (freshDataQ (d * d + (d - 1) * (d - 1)) k q) =
      mkHGPRepStabilizers d i q := by
  rw [scheduleRow_eval_uniform (hgpSchedule d hd i) (hgpKindPauli d i.val)
        (hgpSchedule_support_nodup d hd i)
        (fun slot hslot => by
          rw [hgpSchedule_kind_uniform d hd i slot hslot]
          exact hgpKind_toPauli d i.val)
        (freshDataQ (d * d + (d - 1) * (d - 1)) k q)]
  have hdec : ∀ slot : ScheduledPauli (d * d + (d - 1) * (d - 1)),
      decide (freshDataQ (d * d + (d - 1) * (d - 1)) k slot.qubit
          = freshDataQ (d * d + (d - 1) * (d - 1)) k q)
        = decide (slot.qubit = q) :=
    fun slot => decide_eq_decide.mpr ⟨fun h => freshDataQ_inj h, fun h => by rw [h]⟩
  simp only [hdec]
  have hany : (hgpSchedule d hd i).slots.any (fun slot => decide (slot.qubit = q))
      = ((hgpSchedule d hd i).slots.map (·.qubit)).any (fun qb => decide (qb = q)) := by
    rw [List.any_map]
    rfl
  show (if (hgpSchedule d hd i).slots.any (fun slot => decide (slot.qubit = q))
      then hgpKindPauli d i.val else Pauli.I)
    = QStab.Examples.HGPParametric.stabEntry d i.val q.val
  rw [hany, hgpSchedule_slots_qubits d hd i]
  by_cases hmem : q.val ∈ hgpSupportList d i.val
  · rw [if_pos ?_, stabEntry_mem_supportList d i.val q.val hd i.isLt hmem]
    rw [List.any_map]
    apply List.any_eq_true.mpr
    refine ⟨q.val, hmem, ?_⟩
    show decide (hgpFin d hd q.val = q) = true
    apply decide_eq_true
    apply Fin.ext
    show q.val % (d * d + (d - 1) * (d - 1)) = q.val
    exact Nat.mod_eq_of_lt q.isLt
  · rw [if_neg ?_, stabEntry_eq_I_of_not_mem d i.val q.val hd i.isLt q.isLt hmem]
    intro hc
    rw [List.any_map, List.any_eq_true] at hc
    obtain ⟨q0, hq0, hdq⟩ := hc
    have hq0lt : q0 < d * d + (d - 1) * (d - 1) :=
      hgpSupportList_lt d i.val hd i.isLt q0 hq0
    have heq : hgpFin d hd q0 = q := of_decide_eq_true hdq
    have hval : q0 % (d * d + (d - 1) * (d - 1)) = q.val := congrArg Fin.val heq
    rw [Nat.mod_eq_of_lt hq0lt] at hval
    exact hmem (hval ▸ hq0)

/-- **Triviality on helper qubits.**  The compiled `i`-th stabilizer row is
`I` on every helper qubit. -/
theorem scheduleRow_hgpSchedule_helperTrivial (d : Nat) (hd : 2 ≤ d)
    (i : Fin (2 * ((d - 1) * d))) (k : Nat)
    (q : Fin (d * d + (d - 1) * (d - 1) + k)) (hq : d * d + (d - 1) * (d - 1) ≤ q.val) :
    scheduleRow (k := k) (hgpSchedule d hd i) q = Pauli.I := by
  rw [scheduleRow_eval_uniform (hgpSchedule d hd i) (hgpKindPauli d i.val)
        (hgpSchedule_support_nodup d hd i)
        (fun slot hslot => by
          rw [hgpSchedule_kind_uniform d hd i slot hslot]
          exact hgpKind_toPauli d i.val) q]
  rw [if_neg ?_]
  intro hc
  rw [List.any_eq_true] at hc
  obtain ⟨slot, _, hslot⟩ := hc
  rw [decide_eq_true_eq] at hslot
  have hv := congrArg Fin.val hslot
  rw [freshDataQ_val] at hv
  have := slot.qubit.isLt
  omega

/-! ## The compiled HGP spec and its transports (public aux forms) -/

/-- The compiled HGP PCC spec at distance `d`. -/
def hgpSpec (d : Nat) (hd : 2 ≤ d) :
    CodeSpec (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d)) :=
  fullProgramCodeSpecD (hgpXZProgram d)
    (fullProgramReadoutDisjoint_auto (hgpXZProgram d)) d (by omega)

/-- Source-side data residual of an ambient error state (**public**: the
surface's private analog was a confirmed reuse obstacle). -/
def hgpDataError (d : Nat)
    (es : ErrorState (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d))) :
    ErrorVec (d * d + (d - 1) * (d - 1)) :=
  fun q' => es.paulis
    (freshDataQ (d * d + (d - 1) * (d - 1)) (programHelperCount (hgpXZProgram d)) q')

/-- **The single canonical index equality** — every `Fin.cast` in this file
goes through this proof. -/
theorem hgpNumStab_eq (d : Nat) (hd : 2 ≤ d) :
    (hgpSpec d hd).numStab = (hgpUParams d hd).numStab :=
  programNumStab_hgpXZProgram d hd

/-- The compiled `i`-th stabilizer, read on a data qubit, is the source
generator `(cast i)`. -/
theorem hgp_spec_stab_data (d : Nat) (hd : 2 ≤ d)
    (i : Fin (hgpSpec d hd).numStab) (q' : Fin (d * d + (d - 1) * (d - 1))) :
    (hgpSpec d hd).stabilizer i
        (freshDataQ (d * d + (d - 1) * (d - 1)) (programHelperCount (hgpXZProgram d)) q') =
      (hgpUParams d hd).stabilizers (Fin.cast (hgpNumStab_eq d hd) i) q' := by
  show scheduleRow (k := programHelperCount (hgpXZProgram d))
        ((programMeasuresAt (hgpXZProgram d)).get i).schedule
        (freshDataQ (d * d + (d - 1) * (d - 1)) (programHelperCount (hgpXZProgram d)) q') = _
  rw [hgpXZProgram_schedule_get d hd i,
    scheduleRow_hgpSchedule_dataRestrict d hd _ _ q']
  rfl

/-- The compiled `i`-th stabilizer is `I` on every helper qubit. -/
theorem hgp_spec_stab_helper (d : Nat) (hd : 2 ≤ d)
    (i : Fin (hgpSpec d hd).numStab)
    (q : Fin (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d)))
    (hq : d * d + (d - 1) * (d - 1) ≤ q.val) :
    (hgpSpec d hd).stabilizer i q = Pauli.I := by
  show scheduleRow (k := programHelperCount (hgpXZProgram d))
        ((programMeasuresAt (hgpXZProgram d)).get i).schedule q = _
  rw [hgpXZProgram_schedule_get d hd i]
  exact scheduleRow_hgpSchedule_helperTrivial d hd _ _ q hq

/-- **Value transport on data qubits.** -/
theorem hgp_prodStab_data (d : Nat) (hd : 2 ≤ d)
    (mask : Fin (hgpSpec d hd).numStab → Bool) (q' : Fin (d * d + (d - 1) * (d - 1))) :
    prodStab (hgpSpec d hd) mask
        (freshDataQ (d * d + (d - 1) * (d - 1)) (programHelperCount (hgpXZProgram d)) q') =
      qecMaskProd (hgpUParams d hd)
        (fun i' => mask (Fin.cast (hgpNumStab_eq d hd).symm i')) q' := by
  unfold prodStab
  rw [qecMaskProd_apply]
  exact foldl_transport (hgpNumStab_eq d hd) mask
    (fun i => (hgpSpec d hd).stabilizer i
      (freshDataQ (d * d + (d - 1) * (d - 1)) (programHelperCount (hgpXZProgram d)) q'))
    (fun i' => (hgpUParams d hd).stabilizers i' q')
    (fun i => hgp_spec_stab_data d hd i q') Pauli.I

/-- **Value transport on helper qubits.** -/
theorem hgp_prodStab_helper (d : Nat) (hd : 2 ≤ d)
    (mask : Fin (hgpSpec d hd).numStab → Bool)
    (q : Fin (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d)))
    (hq : d * d + (d - 1) * (d - 1) ≤ q.val) :
    prodStab (hgpSpec d hd) mask q = Pauli.I := by
  unfold prodStab
  exact foldl_pauliMul_allI mask (fun i => (hgpSpec d hd).stabilizer i q)
    (List.finRange _) (fun i _ => hgp_spec_stab_helper d hd i q hq) Pauli.I

/-- **The `k = 0` trick**: `scheduleParity` against a data error equals the
`vectorParity` of the source generator row. -/
theorem hgp_scheduleParity_eq_vectorParity (d : Nat) (hd : 2 ≤ d)
    (i : Fin (2 * ((d - 1) * d))) (E : ErrorVec (d * d + (d - 1) * (d - 1))) :
    scheduleParity (hgpSchedule d hd i) E
      = vectorParity (mkHGPRepStabilizers d i) E := by
  have hrow : mkHGPRepStabilizers d i = scheduleRow (k := 0) (hgpSchedule d hd i) := by
    funext q
    exact (scheduleRow_hgpSchedule_dataRestrict d hd i 0 q).symm
  rw [hrow]
  exact (scheduleRow_vectorParity (k := 0) (hgpSchedule d hd i) E).symm

/-! ## The headline `Stab ↔ InStab` transport -/

/-- **F1 Stab-half over the raw error state** (public aux). -/
theorem hgpNZ_Stab_iff_InStab_es (d : Nat) (hd : 2 ≤ d)
    (es : ErrorState (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d))) :
    Stab (hgpSpec d hd) (dataVector (hgpSpec d hd) es) ↔
      InStab (hgpUParams d hd) (hgpDataError d es) := by
  rw [InStab_iff_qecMaskProd]
  constructor
  · rintro ⟨mask, hmask⟩
    refine ⟨fun i' => mask (Fin.cast (hgpNumStab_eq d hd).symm i'), ?_⟩
    funext q'
    have hq0 := hmask (freshDataQ (d * d + (d - 1) * (d - 1))
      (programHelperCount (hgpXZProgram d)) q')
    rw [hgp_prodStab_data d hd mask q'] at hq0
    rw [← hq0]
    show es.paulis (freshDataQ (d * d + (d - 1) * (d - 1))
        (programHelperCount (hgpXZProgram d)) q')
      = (if (hgpSpec d hd).isData
            (freshDataQ (d * d + (d - 1) * (d - 1))
              (programHelperCount (hgpXZProgram d)) q')
          then es.paulis (freshDataQ (d * d + (d - 1) * (d - 1))
            (programHelperCount (hgpXZProgram d)) q')
          else Pauli.I)
    rw [if_pos (by
      show decide ((freshDataQ (d * d + (d - 1) * (d - 1))
          (programHelperCount (hgpXZProgram d)) q').val
          < d * d + (d - 1) * (d - 1)) = true
      rw [freshDataQ_val]
      exact decide_eq_true q'.isLt)]
  · rintro ⟨mask', hmask'⟩
    refine ⟨fun i => mask' (Fin.cast (hgpNumStab_eq d hd) i), ?_⟩
    intro q
    by_cases hq : q.val < d * d + (d - 1) * (d - 1)
    · have hqeq : q = freshDataQ (d * d + (d - 1) * (d - 1))
          (programHelperCount (hgpXZProgram d)) ⟨q.val, hq⟩ :=
        Fin.ext (by rw [freshDataQ_val])
      rw [hqeq, hgp_prodStab_data d hd
        (fun i => mask' (Fin.cast (hgpNumStab_eq d hd) i)) ⟨q.val, hq⟩]
      show (if (hgpSpec d hd).isData
              (freshDataQ (d * d + (d - 1) * (d - 1))
                (programHelperCount (hgpXZProgram d)) ⟨q.val, hq⟩)
            then es.paulis (freshDataQ (d * d + (d - 1) * (d - 1))
              (programHelperCount (hgpXZProgram d)) ⟨q.val, hq⟩)
            else Pauli.I) = _
      rw [if_pos (by
        show decide ((freshDataQ (d * d + (d - 1) * (d - 1))
            (programHelperCount (hgpXZProgram d)) ⟨q.val, hq⟩).val
            < d * d + (d - 1) * (d - 1)) = true
        rw [freshDataQ_val]
        exact decide_eq_true hq)]
      have hcast : (fun i' => mask' (Fin.cast (hgpNumStab_eq d hd)
          (Fin.cast (hgpNumStab_eq d hd).symm i'))) = mask' := by
        funext i'
        exact congrArg mask' (Fin.ext rfl)
      rw [hcast]
      exact congrFun hmask' ⟨q.val, hq⟩
    · have hq' : d * d + (d - 1) * (d - 1) ≤ q.val := Nat.le_of_not_lt hq
      rw [hgp_prodStab_helper d hd
        (fun i => mask' (Fin.cast (hgpNumStab_eq d hd) i)) q hq']
      show (if (hgpSpec d hd).isData q then es.paulis q else Pauli.I) = Pauli.I
      rw [if_neg (by
        show ¬ (decide (q.val < d * d + (d - 1) * (d - 1)) = true)
        rw [decide_eq_true_eq]
        exact hq)]

/-- **F1 Stab-half (public `QCState` form).** -/
theorem hgpNZ_Stab_iff_InStab (d : Nat) (hd : 2 ≤ d)
    (sigma : QCState (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d))) :
    Stab (hgpSpec d hd) (dataVector (hgpSpec d hd) sigma.es) ↔
      InStab (hgpUParams d hd)
        (dataErrorOfQCState (hgpUParams d hd)
          (programHelperCount (hgpXZProgram d)) sigma) :=
  hgpNZ_Stab_iff_InStab_es d hd sigma.es

/-! ## The `Centralizer` half and the assembled `logicalFailure` iff -/

/-- **Centralizer transport over the raw error state** (public aux, native
`ErrorVec.parity` form). -/
theorem hgpNZ_centralizer_iff_es (d : Nat) (hd : 2 ≤ d)
    (es : ErrorState (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d))) :
    Centralizer (hgpSpec d hd) (dataVector (hgpSpec d hd) es) ↔
      ∀ j : Fin (hgpUParams d hd).numStab,
        ErrorVec.parity ((hgpUParams d hd).stabilizers j) (hgpDataError d es) = false := by
  refine Iff.trans (compiled_centralizer_transport (hgpXZProgram d)
    (fullProgramReadoutDisjoint_auto (hgpXZProgram d)) d (by omega) es) ?_
  show (∀ i : Fin (programNumStab (hgpXZProgram d)),
      scheduleParity ((programMeasuresAt (hgpXZProgram d)).get i).schedule
        (hgpDataError d es) = false) ↔ _
  have hbridge : ∀ i : Fin (programNumStab (hgpXZProgram d)),
      scheduleParity ((programMeasuresAt (hgpXZProgram d)).get i).schedule
          (hgpDataError d es)
        = ErrorVec.parity ((hgpUParams d hd).stabilizers
            (Fin.cast (hgpNumStab_eq d hd) i)) (hgpDataError d es) := by
    intro i
    rw [hgpXZProgram_schedule_get d hd i,
      hgp_scheduleParity_eq_vectorParity d hd _ (hgpDataError d es),
      vectorParity_eq_parity]
    rfl
  simp only [hbridge]
  exact Fin_cast_forall_iff (hgpNumStab_eq d hd)
    (fun j => ErrorVec.parity ((hgpUParams d hd).stabilizers j)
      (hgpDataError d es) = false)

/-- **The parametric `logicalFailure` bridge (public form).**  The compiled
HGP spec's `logicalFailure` is a purely source-side statement: the data
residual commutes with every `hgpUParams` generator and is not a source
stabilizer product. -/
theorem hgpNZ_logicalFailure_iff (d : Nat) (hd : 2 ≤ d)
    (sigma : QCState (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d))) :
    QStab.QClifford.PCC.logicalFailure (hgpSpec d hd) sigma.es ↔
      ((∀ j : Fin (hgpUParams d hd).numStab,
          ErrorVec.parity ((hgpUParams d hd).stabilizers j)
            (dataErrorOfQCState (hgpUParams d hd)
              (programHelperCount (hgpXZProgram d)) sigma) = false)
        ∧ ¬ InStab (hgpUParams d hd)
            (dataErrorOfQCState (hgpUParams d hd)
              (programHelperCount (hgpXZProgram d)) sigma)) := by
  show QStab.QClifford.PCC.logicalFailure (hgpSpec d hd) sigma.es ↔
    ((∀ j : Fin (hgpUParams d hd).numStab,
        ErrorVec.parity ((hgpUParams d hd).stabilizers j)
          (hgpDataError d sigma.es) = false)
      ∧ ¬ InStab (hgpUParams d hd) (hgpDataError d sigma.es))
  unfold QStab.QClifford.PCC.logicalFailure
  exact and_congr (hgpNZ_centralizer_iff_es d hd sigma.es)
    (not_congr (hgpNZ_Stab_iff_InStab_es d hd sigma.es))

-- Regression guards (axiom pins) for the transport headliners.
/--
info: 'QStab.QClifford.Compile.stabEntry_eq_I_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stabEntry_eq_I_of_not_mem

/--
info: 'QStab.QClifford.Compile.scheduleRow_hgpSchedule_dataRestrict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scheduleRow_hgpSchedule_dataRestrict

/--
info: 'QStab.QClifford.Compile.hgpNZ_Stab_iff_InStab' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpNZ_Stab_iff_InStab

/--
info: 'QStab.QClifford.Compile.hgpNZ_logicalFailure_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpNZ_logicalFailure_iff

end QStab.QClifford.Compile
