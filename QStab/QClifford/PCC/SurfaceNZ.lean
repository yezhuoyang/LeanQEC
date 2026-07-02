import QStab.QClifford.Compile.Calculus
import QStab.Examples.SurfaceHookErrors
import QStab.QHL.Verify.SurfaceCharEval

/-!
# Surface/NZ source program and its compilation (Workstream C0 / S1)

This file defines the **source** Surface/NZ measurement program as a
compiler-facing `XZProgram`, built entirely from the already-proven parametric
surface geometry (`classifyStab`, `kindOrderRC`, `numStabFormula`,
`mkSurfaceStabilizers` in `QStab.Examples.SurfaceParametric`).  The target
circuit is then the **compiler output** `compileProgram (surfaceXZProgram d)` —
never hand-written — so `programEq`/`syn` check the genuine compilation.

The NZ schedule is exactly `kindOrderRC d (classifyStab d i)` — the same
ordering from which the source back-action set `mkSurfaceHookErrors` is derived
— so the compiled circuit's fault structure is consistent with the source
`NZSurfaceSpec`/`mkSurfaceQECParams` certificate.
-/

namespace QStab.QClifford.PCC.SurfaceNZ

open QStab.QClifford.Compile
open QStab.Examples.SurfaceParametric

/-- The CSS Pauli kind (X or Z) of each surface stabilizer kind. -/
def kindXZ : StabKind → XZPauli
  | .bulkZ _ _ => .Z
  | .bulkX _ _ => .X
  | .topX _    => .X
  | .rightZ _  => .Z
  | .leftZ _   => .Z
  | .bottomX _ => .X

/-- Total `Fin (d*d)` index for a grid coordinate `(row, col)`.  For in-range
coordinates (`row, col < d`) it equals `gridIdx d row col`; the modulus keeps it
total without a per-coordinate range proof. -/
def gridFin (d : Nat) (hd : 0 < d) (rc : Nat × Nat) : Fin (d * d) :=
  ⟨(d * rc.1 + rc.2) % (d * d), Nat.mod_lt _ (Nat.mul_pos hd hd)⟩

/-- The NZ `RuleSchedule` for surface stabilizer `i`: its support listed in NZ
order (`kindOrderRC`), all of the one CSS kind (`kindXZ`). -/
def nzSchedule (d : Nat) (hd : 0 < d) (i : Fin (numStabFormula d)) :
    RuleSchedule (d * d) :=
  RuleSchedule.uniform (kindXZ (classifyStab d i.val))
    ((kindOrderRC d (classifyStab d i.val)).map (gridFin d hd))

/-- The Surface/NZ **source** program (compiler-facing `XZProgram`): measure
every stabilizer via the NZ scheme with its NZ schedule, in index order. -/
def surfaceXZProgram (d : Nat) (hd : 0 < d) : XZProgram (d * d) :=
  (List.finRange (numStabFormula d)).foldr
    (fun i acc => .seq (.meas .NZ (nzSchedule d hd i)) acc) .skip

/-- The compiled **target** circuit is the compiler output on the source
program — not hand-written. -/
def surfaceCircuit (d : Nat) (hd : 0 < d) :
    FCircuit ((d * d) + programHelperCount (surfaceXZProgram d hd)) :=
  compileProgram (surfaceXZProgram d hd)

/-! ## Sanity checks (reduce to closed literals) -/

-- d=3: 8 stabilizer measurements.
#eval (List.finRange (numStabFormula 3)).length      -- 8
-- stabilizer 0 at d=3 is bulk-Z → NZ schedule of length 4.
#eval (nzSchedule 3 (by decide) ⟨0, by decide⟩).slots.length   -- 4
-- the schedule qubits of stabilizer 0 at d=3 (bulkZ (0,0)): [0,3,1,4].
#eval (RuleSchedule.support (nzSchedule 3 (by decide) ⟨0, by decide⟩)).map Fin.val

/-! ## Code-eval foundation (the faithful stabilizer content)

The stabilizer *content* must come from the core recursive stabilizer program
`Surface.code`, not from the uncertified meta decoder `decodeStabPauliAt`.
`surfaceCellPauli d k q` (namespace `QHL.CodeLang.Surface.Verify`) is exactly
that: `recCall_eval_surfaceCellPauli` proves, for every `OddSurfaceDistance`,
`Term.eval Surface.code.body … (.stabAt (.recCall d k) q) = some (surfaceCellPauli d k q)`
— the *certified object-language evaluation* of the code, decide-free.

So the regenerated foundation grounds the stabilizer content on `surfaceCellPauli`.
The remaining obligation (schedule faithfulness) is: the NZ schedule
`nzSchedule d i` orders exactly the support of `surfaceCellPauli d i` with the
matching CSS kind — tying the compiler-facing schedule back to the code eval. -/

open QHL.CodeLang.Surface.Verify (surfaceCellPauli)

-- Cross-check: at d=3, stabilizer 0's NZ schedule support `[0,3,1,4]` all carry
-- `Z` under the CODE evaluation, and off-support qubit 2 is `I`.
#eval [0, 3, 1, 4].map (surfaceCellPauli 3 0)   -- [Z, Z, Z, Z]
#eval surfaceCellPauli 3 0 2                     -- I

end QStab.QClifford.PCC.SurfaceNZ
