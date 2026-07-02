import QStab.QClifford.Compile.SurfaceNZVCGen

/-!
# F1 foundation: the schedule alignment linchpin

The compiled spec's `i`-th stabilizer row is `scheduleRow` of the `i`-th *measured*
schedule, `((programMeasuresAt (surfaceXZProgram d hd)).get i).schedule`.  To connect it to
`nzSchedule d hd i` (and hence, via piece 2, to `mkSurfaceStabilizers`), we need that
measured schedule to *be* `nzSchedule d hd i`.  This file proves it, via a general fact
about `foldr`-of-`seq`-`meas` programs (reusable — HGP's alignment will want it too), and
derives `programNumStab_surfaceXZProgram`.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.QClifford.PCC.SurfaceNZ
open QStab.Examples.SurfaceParametric

/-- **The measured schedules of a `foldr`-of-`seq`-`meas` program are the mapped
schedules.**  Independent of the helper/detector offsets and the fit proofs (the
`.schedule` projection reads none of them). -/
theorem measuresAtAux_seqMeas_map_schedule {n th tf : Nat} {α : Type}
    (g : α → RuleSchedule n) :
    ∀ (L : List α) (hs ds : Nat)
      (fit : hs + programHelperCount
        (L.foldr (fun a acc => XZProgram.seq (.meas Scheme.NZ (g a)) acc) XZProgram.skip) ≤ th)
      (dfit : ds + programDetectorCount
        (L.foldr (fun a acc => XZProgram.seq (.meas Scheme.NZ (g a)) acc) XZProgram.skip) ≤ tf),
      ((programMeasuresAtAux (totalHelpers := th) (totalFlags := tf) hs ds
        (L.foldr (fun a acc => XZProgram.seq (.meas Scheme.NZ (g a)) acc) XZProgram.skip)
        fit dfit).map (·.schedule)) = L.map g := by
  intro L
  induction L with
  | nil => intro hs ds fit dfit; rfl
  | cons a rest ih =>
      intro hs ds fit dfit
      simp only [List.foldr_cons, programMeasuresAtAux, List.map_cons, List.singleton_append]
      exact congrArg (g a :: ·) (ih _ _ _ _)

/-- The measured schedules of `surfaceXZProgram` are the `nzSchedule` family. -/
theorem surfaceXZProgram_map_schedule (d : Nat) (hd : 0 < d) :
    (programMeasuresAt (surfaceXZProgram d hd)).map (·.schedule) =
      (List.finRange (numStabFormula d)).map (nzSchedule d hd) := by
  unfold programMeasuresAt surfaceXZProgram
  exact measuresAtAux_seqMeas_map_schedule (nzSchedule d hd) (List.finRange (numStabFormula d))
    0 0 _ _

/-- **Stabilizer count:** the compiled surface program measures exactly `numStabFormula d`
generators. -/
theorem programNumStab_surfaceXZProgram (d : Nat) (hd : 0 < d) :
    programNumStab (surfaceXZProgram d hd) = numStabFormula d := by
  unfold programNumStab
  have h := surfaceXZProgram_map_schedule d hd
  have hl := congrArg List.length h
  simpa using hl

/-- **Schedule-at-`i` alignment:** the `i`-th measured schedule of the compiled surface
program is `nzSchedule d hd i` (the index cast along `programNumStab_surfaceXZProgram`). -/
theorem surfaceXZProgram_schedule_get (d : Nat) (hd : 0 < d)
    (i : Fin (programNumStab (surfaceXZProgram d hd))) :
    ((programMeasuresAt (surfaceXZProgram d hd)).get i).schedule =
      nzSchedule d hd (Fin.cast (programNumStab_surfaceXZProgram d hd) i) := by
  have h := surfaceXZProgram_map_schedule d hd
  have hi2 : i.val < numStabFormula d := by
    rw [← programNumStab_surfaceXZProgram d hd]; exact i.isLt
  have key : ((programMeasuresAt (surfaceXZProgram d hd)).map (·.schedule))[i.val]?
      = ((List.finRange (numStabFormula d)).map (nzSchedule d hd))[i.val]? := by rw [h]
  rw [List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem
      (show i.val < (programMeasuresAt (surfaceXZProgram d hd)).length from i.isLt),
    List.getElem?_eq_getElem (by rw [List.length_finRange]; exact hi2)] at key
  simp only [Option.map_some, Option.some.injEq, List.getElem_finRange] at key
  rw [List.get_eq_getElem, key]
  congr 1

end QStab.QClifford.Compile
