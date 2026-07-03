import QStab.QClifford.Compile.SurfaceNZStabBridge
import QStab.Examples.SurfaceHookErrors
import QStab.QClifford.Compile.HoarePreservation

/-!
# F1 Stab-half: the dimensional transport `Stab (compiled) ↔ InStab (source)`

`InStab_iff_qecMaskProd` (in `SurfaceNZStabBridge`) characterises the source stabilizer
subgroup as masked products over `Fin (d*d)`.  The compiled PCC spec's `Stab`/`prodStab`
predicates instead live over `Fin (d*d + k)` (data + `k` helpers) and fold with the
kernel's `pauliMul`.  This file bridges the two:

* the *value* transport `prodStab (compiled) mask (freshDataQ q') = qecMaskProd (source)
  (mask ∘ cast) q'` on data qubits, and `= I` on helper qubits — driven by the schedule
  alignment (`surfaceXZProgram_schedule_get`) and the faithfulness lemmas
  (`scheduleRow_nzSchedule_dataRestrict` / `_helperTrivial`) of piece (2);
* the *index* transport, a `Fin.cast` along `programNumStab_surfaceXZProgram`, handled once
  in the general `foldl_finRange_cast`;
* the assembled headline `surfaceNZ_Stab_iff_InStab`.

Everything is decide-free and parametric in odd `d ≥ 3`.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.QClifford.PCC.SurfaceNZ
open QStab.Examples.SurfaceParametric

/-! ## Surface-specific value transport -/

/-- Abbreviation for the compiled surface spec. -/
private def surfSpec (d : Nat) (hd : 0 < d) :
    CodeSpec (d * d + programHelperCount (surfaceXZProgram d hd)) :=
  fullProgramCodeSpecD (surfaceXZProgram d hd)
    (fullProgramReadoutDisjoint_auto (surfaceXZProgram d hd)) d hd

/-- Source-side data-qubit residual of an ambient error state. -/
private def surfDataError (d : Nat) (hd : 0 < d)
    (es : ErrorState (d * d + programHelperCount (surfaceXZProgram d hd))) : ErrorVec (d * d) :=
  fun q' => es.paulis (freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd)) q')

/-- **The single canonical index equality** between the compiled spec's stabilizer count and
the source `QECParams`' — every `Fin.cast` in this file goes through *this* proof, so the
folded masks land at one spelling and syntactic `rw` matching never fights a cast motive.
Definitionally `programNumStab_surfaceXZProgram`. -/
private theorem surfNumStab_eq (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) :
    (surfSpec d hd).numStab = (mkSurfaceQECParams d hd hodd).numStab :=
  programNumStab_surfaceXZProgram d hd

/-- The compiled `i`-th stabilizer, read on a data qubit, is the source generator `(cast i)`
(via schedule alignment + on-data faithfulness). -/
private theorem spec_stab_data (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (i : Fin (surfSpec d hd).numStab) (q' : Fin (d * d)) :
    (surfSpec d hd).stabilizer i
        (freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd)) q') =
      (mkSurfaceQECParams d hd hodd).stabilizers
        (Fin.cast (surfNumStab_eq d hd hodd) i) q' := by
  show scheduleRow (k := programHelperCount (surfaceXZProgram d hd))
        ((programMeasuresAt (surfaceXZProgram d hd)).get i).schedule
        (freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd)) q') = _
  rw [surfaceXZProgram_schedule_get d hd i,
    scheduleRow_nzSchedule_dataRestrict hd hd3 hodd _ _ q']
  rfl

/-- The compiled `i`-th stabilizer is `I` on every helper qubit. -/
private theorem spec_stab_helper (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (i : Fin (surfSpec d hd).numStab)
    (q : Fin (d * d + programHelperCount (surfaceXZProgram d hd))) (hq : d * d ≤ q.val) :
    (surfSpec d hd).stabilizer i q = Pauli.I := by
  show scheduleRow (k := programHelperCount (surfaceXZProgram d hd))
        ((programMeasuresAt (surfaceXZProgram d hd)).get i).schedule q = _
  rw [surfaceXZProgram_schedule_get d hd i]
  exact scheduleRow_nzSchedule_helperTrivial hd hd3 hodd _ _ q hq

/-- **Value transport on data qubits.**  The compiled masked product, read on a data qubit,
is the source masked product with the inverse-cast mask. -/
private theorem prodStab_data (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (mask : Fin (surfSpec d hd).numStab → Bool) (q' : Fin (d * d)) :
    prodStab (surfSpec d hd) mask
        (freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd)) q') =
      qecMaskProd (mkSurfaceQECParams d hd hodd)
        (fun i' => mask (Fin.cast (surfNumStab_eq d hd hodd).symm i')) q' := by
  unfold prodStab
  rw [qecMaskProd_apply]
  exact foldl_transport (surfNumStab_eq d hd hodd) mask
    (fun i => (surfSpec d hd).stabilizer i
      (freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd)) q'))
    (fun i' => (mkSurfaceQECParams d hd hodd).stabilizers i' q')
    (fun i => spec_stab_data d hd hd3 hodd i q') Pauli.I

/-- **Value transport on helper qubits.**  The compiled masked product is `I` off the data
block. -/
private theorem prodStab_helper (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (mask : Fin (surfSpec d hd).numStab → Bool)
    (q : Fin (d * d + programHelperCount (surfaceXZProgram d hd))) (hq : d * d ≤ q.val) :
    prodStab (surfSpec d hd) mask q = Pauli.I := by
  unfold prodStab
  exact foldl_pauliMul_allI mask (fun i => (surfSpec d hd).stabilizer i q)
    (List.finRange _) (fun i _ => spec_stab_helper d hd hd3 hodd i q hq) Pauli.I

/-! ## Parity bridges: `scheduleParity` → `vectorParity` → `ErrorVec.parity` -/

/-- **The `k = 0` trick.**  A schedule's `scheduleParity` against a `d*d`-error equals the
`vectorParity` of the corresponding surface stabilizer row — read the row as a `k = 0`
`scheduleRow` (whose faithfulness is exactly `scheduleRow_nzSchedule_dataRestrict`) and
apply `scheduleRow_vectorParity`.  This is the missing step that lets the compiled
`Centralizer` obligation speak the source geometry's `ErrorVec.parity` language. -/
theorem scheduleParity_eq_vectorParity (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) (j : Fin (numStabFormula d)) (E : ErrorVec (d * d)) :
    scheduleParity (nzSchedule d hd j) E = vectorParity (mkSurfaceStabilizers d hd j) E := by
  have hrow : mkSurfaceStabilizers d hd j = scheduleRow (k := 0) (nzSchedule d hd j) := by
    funext q
    exact (scheduleRow_nzSchedule_dataRestrict hd hd3 hodd j 0 q).symm
  rw [hrow, scheduleRow_vectorParity (k := 0) (nzSchedule d hd j) E]
  rfl

/-! ## The headline `Stab ↔ InStab` transport -/

/-- Proof-side (private-abbreviation) form of the Stab-half. -/
private theorem surfaceNZ_Stab_iff_InStab_aux (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (es : ErrorState (d * d + programHelperCount (surfaceXZProgram d hd))) :
    Stab (surfSpec d hd) (dataVector (surfSpec d hd) es) ↔
      InStab (mkSurfaceQECParams d hd hodd) (surfDataError d hd es) := by
  rw [InStab_iff_qecMaskProd]
  constructor
  · rintro ⟨mask, hmask⟩
    refine ⟨fun i' => mask (Fin.cast (surfNumStab_eq d hd hodd).symm i'), ?_⟩
    funext q'
    have hq0 := hmask (freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd)) q')
    rw [prodStab_data d hd hd3 hodd mask q'] at hq0
    rw [← hq0]
    show es.paulis (freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd)) q')
        = (if (surfSpec d hd).isData
              (freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd)) q')
            then es.paulis (freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd)) q')
            else Pauli.I)
    rw [if_pos (by
      show decide ((freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd)) q').val
          < d * d) = true
      rw [freshDataQ_val]; exact decide_eq_true q'.isLt)]
  · rintro ⟨mask', hmask'⟩
    refine ⟨fun i => mask' (Fin.cast (surfNumStab_eq d hd hodd) i), ?_⟩
    intro q
    by_cases hq : q.val < d * d
    · have hqeq : q = freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd)) ⟨q.val, hq⟩ :=
        Fin.ext (by rw [freshDataQ_val])
      rw [hqeq, prodStab_data d hd hd3 hodd
        (fun i => mask' (Fin.cast (surfNumStab_eq d hd hodd) i)) ⟨q.val, hq⟩]
      show (if (surfSpec d hd).isData
                (freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd)) ⟨q.val, hq⟩)
              then es.paulis
                (freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd)) ⟨q.val, hq⟩)
              else Pauli.I) = _
      rw [if_pos (by
        show decide ((freshDataQ (d * d) (programHelperCount (surfaceXZProgram d hd))
            ⟨q.val, hq⟩).val < d * d) = true
        rw [freshDataQ_val]; exact decide_eq_true hq)]
      have hcast : (fun i' => mask' (Fin.cast (surfNumStab_eq d hd hodd)
          (Fin.cast (surfNumStab_eq d hd hodd).symm i'))) = mask' := by
        funext i'; exact congrArg mask' (Fin.ext rfl)
      rw [hcast]
      exact congrFun hmask' ⟨q.val, hq⟩
    · have hq' : d * d ≤ q.val := Nat.le_of_not_lt hq
      rw [prodStab_helper d hd hd3 hodd
        (fun i => mask' (Fin.cast (surfNumStab_eq d hd hodd) i)) q hq']
      show (if (surfSpec d hd).isData q then es.paulis q else Pauli.I) = Pauli.I
      rw [if_neg (by
        show ¬ (decide (q.val < d * d) = true)
        rw [decide_eq_true_eq]; exact hq)]

/-- **F1 Stab-half (public form).**  The compiled surface spec's `Stab` predicate on the
data vector is equivalent to the source `InStab` predicate on the data residual.  Stated in
public pipeline names (`fullProgramCodeSpecD (surfaceXZProgram …)`, `mkSurfaceQECParams`,
`dataErrorOfQCState`), so the whole statement is auditable against the pipeline. -/
theorem surfaceNZ_Stab_iff_InStab (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (sigma : QCState (d * d + programHelperCount (surfaceXZProgram d hd))) :
    Stab (fullProgramCodeSpecD (surfaceXZProgram d hd)
            (fullProgramReadoutDisjoint_auto (surfaceXZProgram d hd)) d hd)
        (dataVector (fullProgramCodeSpecD (surfaceXZProgram d hd)
            (fullProgramReadoutDisjoint_auto (surfaceXZProgram d hd)) d hd) sigma.es) ↔
      InStab (mkSurfaceQECParams d hd hodd)
        (dataErrorOfQCState (mkSurfaceQECParams d hd hodd)
          (programHelperCount (surfaceXZProgram d hd)) sigma) :=
  surfaceNZ_Stab_iff_InStab_aux d hd hd3 hodd sigma.es

/-! ## The `Centralizer` half in native `ErrorVec.parity` form -/

/-- **Centralizer transport (native parity form).**  The compiled spec's `Centralizer`
obligation on the data vector is equivalent to: the source data residual commutes (in
`ErrorVec.parity`) with every `mkSurfaceQECParams` generator.  Chains
`compiled_centralizer_transport` (→ `scheduleParity`), the `k = 0` trick
(`scheduleParity_eq_vectorParity`), and `vectorParity_eq_parity`, then reindexes. -/
private theorem surfaceNZ_centralizer_iff_aux (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (es : ErrorState (d * d + programHelperCount (surfaceXZProgram d hd))) :
    Centralizer (surfSpec d hd) (dataVector (surfSpec d hd) es) ↔
      ∀ j : Fin (mkSurfaceQECParams d hd hodd).numStab,
        ErrorVec.parity ((mkSurfaceQECParams d hd hodd).stabilizers j)
          (surfDataError d hd es) = false := by
  refine Iff.trans (compiled_centralizer_transport (surfaceXZProgram d hd)
    (fullProgramReadoutDisjoint_auto (surfaceXZProgram d hd)) d hd es) ?_
  show (∀ i : Fin (programNumStab (surfaceXZProgram d hd)),
      scheduleParity ((programMeasuresAt (surfaceXZProgram d hd)).get i).schedule
        (surfDataError d hd es) = false) ↔ _
  have hbridge : ∀ i : Fin (programNumStab (surfaceXZProgram d hd)),
      scheduleParity ((programMeasuresAt (surfaceXZProgram d hd)).get i).schedule
          (surfDataError d hd es)
        = ErrorVec.parity ((mkSurfaceQECParams d hd hodd).stabilizers
            (Fin.cast (surfNumStab_eq d hd hodd) i)) (surfDataError d hd es) := by
    intro i
    rw [surfaceXZProgram_schedule_get d hd i,
      scheduleParity_eq_vectorParity d hd hd3 hodd _ (surfDataError d hd es),
      vectorParity_eq_parity]
    rfl
  simp only [hbridge]
  exact Fin_cast_forall_iff (surfNumStab_eq d hd hodd)
    (fun j => ErrorVec.parity ((mkSurfaceQECParams d hd hodd).stabilizers j)
      (surfDataError d hd es) = false)

/-! ## The assembled `logicalFailure` characterisation (public, native parity) -/

/-- **F1 Stab-half — the parametric `logicalFailure` bridge (public form).**  The compiled
PCC spec's `logicalFailure` on a clean-start state is equivalent to a purely *source-side*
statement about the data residual: it commutes (`ErrorVec.parity`) with every
`mkSurfaceQECParams` generator (the `Centralizer` half) and is *not* a source stabilizer
(`¬ InStab`, the `Stab` half).  Every position of the PCC `logicalFailure` is rewritten
into public pipeline names. -/
theorem surfaceNZ_logicalFailure_iff (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (sigma : QCState (d * d + programHelperCount (surfaceXZProgram d hd))) :
    QStab.QClifford.PCC.logicalFailure (fullProgramCodeSpecD (surfaceXZProgram d hd)
        (fullProgramReadoutDisjoint_auto (surfaceXZProgram d hd)) d hd) sigma.es ↔
      ((∀ j : Fin (mkSurfaceQECParams d hd hodd).numStab,
          ErrorVec.parity ((mkSurfaceQECParams d hd hodd).stabilizers j)
            (dataErrorOfQCState (mkSurfaceQECParams d hd hodd)
              (programHelperCount (surfaceXZProgram d hd)) sigma) = false)
        ∧ ¬ InStab (mkSurfaceQECParams d hd hodd)
            (dataErrorOfQCState (mkSurfaceQECParams d hd hodd)
              (programHelperCount (surfaceXZProgram d hd)) sigma)) := by
  show QStab.QClifford.PCC.logicalFailure (surfSpec d hd) sigma.es ↔
    ((∀ j : Fin (mkSurfaceQECParams d hd hodd).numStab,
        ErrorVec.parity ((mkSurfaceQECParams d hd hodd).stabilizers j)
          (surfDataError d hd sigma.es) = false)
      ∧ ¬ InStab (mkSurfaceQECParams d hd hodd) (surfDataError d hd sigma.es))
  unfold QStab.QClifford.PCC.logicalFailure
  exact and_congr (surfaceNZ_centralizer_iff_aux d hd hd3 hodd sigma.es)
    (not_congr (surfaceNZ_Stab_iff_InStab_aux d hd hd3 hodd sigma.es))

end QStab.QClifford.Compile
