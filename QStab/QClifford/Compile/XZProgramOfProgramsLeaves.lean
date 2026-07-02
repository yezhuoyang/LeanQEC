import QStab.QClifford.Compile.XZProgramOfPrograms
import QStab.QClifford.Compile.SurfaceHValid

/-!
# Generic measurement-leaf facts for the two-program generator

The generator-level analogue of `surfaceXZProgram_allNZ` /
`surfaceXZProgram_measLeaf`, proved once for **every** code family: the
generator only emits `.meas .NZ` leaves, and every leaf's schedule is
`genSchedule … k` for some `k < numStab`.  Surface, Steane and HGP consume
these instead of re-proving per-code pinning lemmas.

(Placed beside — not inside — the code-blind generator file only because
`MeasLeaf` currently lives in `SurfaceHValid`; the statements are fully
code-blind.)
-/

namespace QStab.QClifford.Compile

open QHL.CodeLang

/-- The generator emits only `.meas .NZ` leaves. -/
theorem xzProgramOfPrograms_allNZ (code : CodeFn) (orderProg : Term 3 .nat)
    (lenProg : Term 2 .nat) (numStab nQ d : Nat) :
    XZProgram.allNZ (xzProgramOfPrograms code orderProg lenProg numStab nQ d) := by
  unfold xzProgramOfPrograms
  induction List.range numStab with
  | nil => exact True.intro
  | cons k rest ih => exact ⟨rfl, ih⟩

/-- Every measurement leaf of a generator-shaped fold is one of its per-`k`
    schedules (generic in the per-index schedule function). -/
theorem foldr_measLeaf_range {nQ : Nat} (f : Nat → RuleSchedule nQ) (l : List Nat)
    (scheme : Scheme) (sigma : RuleSchedule nQ) :
    MeasLeaf (l.foldr (fun k acc => .seq (.meas .NZ (f k)) acc) .skip) scheme sigma →
      ∃ k ∈ l, scheme = Scheme.NZ ∧ sigma = f k := by
  induction l with
  | nil => intro h; cases h
  | cons k rest ih =>
      intro h
      cases h with
      | left hleft => cases hleft; exact ⟨k, List.mem_cons_self, rfl, rfl⟩
      | right hright =>
          obtain ⟨k', hk', hs, hσ⟩ := ih hright
          exact ⟨k', List.mem_cons_of_mem _ hk', hs, hσ⟩

/-- **Every measurement leaf of the generated program is
    `(.NZ, genSchedule … k)` for some `k < numStab`.** -/
theorem xzProgramOfPrograms_measLeaf (code : CodeFn) (orderProg : Term 3 .nat)
    (lenProg : Term 2 .nat) (numStab nQ d : Nat)
    (scheme : Scheme) (sigma : RuleSchedule nQ) :
    MeasLeaf (xzProgramOfPrograms code orderProg lenProg numStab nQ d) scheme sigma →
      ∃ k, k < numStab ∧ scheme = Scheme.NZ ∧
        sigma = genSchedule code orderProg lenProg nQ d k := by
  intro h
  obtain ⟨k, hk, hs, hσ⟩ := foldr_measLeaf_range _ _ _ _ h
  exact ⟨k, List.mem_range.mp hk, hs, hσ⟩

#print axioms xzProgramOfPrograms_allNZ
#print axioms xzProgramOfPrograms_measLeaf

end QStab.QClifford.Compile
