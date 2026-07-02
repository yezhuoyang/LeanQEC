import QStab.QClifford.Compile.XZProgramOfPrograms
import QStab.QClifford.Compile.SurfaceNZScheduleAnchor
import QStab.QHL.CodeSurfaceScheduleEval
import QStab.QHL.Verify.SurfaceBridgeDefined

/-!
# S3b: re-anchoring the two-program generator to `surfaceXZProgram`

This is the **anchor section** — the only place the code-blind generator
(`XZProgramOfPrograms`) meets the surface code.  Its imports (surface files) make the
separation auditable: the generator file imports nothing surface-specific; every surface
dependency of the re-anchor lives here.

Goal (odd `d ≥ 3`):
`xzProgramOfPrograms Surface.code nzOrderProg nzLenProg (d*d - 1) (d*d) d = surfaceXZProgram d hd`,
whence `surfaceCircuit d hd = compileProgram (xzProgramOfPrograms …)` transfers every
closed headline to the two-program pipeline.

This file currently lands the reusable **foundation** lemmas; the per-`k` schedule
equality + the `List.range`/`List.finRange` foldr bridge + the final anchor are assembled
on top of them.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford
open QStab.QClifford.PCC.SurfaceNZ
open QStab.Examples.SurfaceParametric
open QHL.CodeLang
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.Verify
open QHL.CodeLang.Verify
open QHL.CodeSurfaceSchedule

/-- Reconstruct the `OddSurfaceDistance` witness for an odd `d ≥ 3` (`d = 2m + 3`). -/
def oddDist (d : Nat) : OddSurfaceDistance := ⟨(d - 3) / 2⟩

/-- The reconstructed witness has the intended distance. -/
theorem oddDist_distance (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    (oddDist d).distance = d := by
  show OddSurfaceDistance.distance ⟨(d - 3) / 2⟩ = d
  unfold OddSurfaceDistance.distance oddDistance
  show 2 * ((d - 3) / 2) + 3 = d
  omega

/-- **`evalAt?` agreement.**  For odd `d ≥ 3`, the code's evaluated Pauli at `(k, q)` is
exactly `surfaceCellPauli` — the certified bridge, un-wrapped from `OddSurfaceDistance`
(so downstream code sees a plain `d`, not an index). -/
theorem surface_evalAt_eq_cellPauli (d k q : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    Surface.code.evalAt? d k q = some (surfaceCellPauli d k q) := by
  have hD : (oddDist d).distance = d := oddDist_distance d hd3 hodd
  have h := evalEntry_surfaceCellPauli (oddDist d) k q
  rw [hD] at h
  exact h

/-- **The kind default never fires.**  Every CSS stabilizer kind is `X` or `Z` (never
`I`/`Y`), so reading it back through `kindOfPauli` is faithful: `kindOfPauli (kindPauli k)
= kindXZ k`.  This is the named justification that the generator's arbitrary `I`/`Y`/none
fallback is unreachable in the anchor. -/
theorem kindOfPauli_kindPauli (k : StabKind) :
    kindOfPauli (some (kindPauli k)) = kindXZ k := by
  cases k <;> rfl

/-- **Qubit reconciliation.**  The `gridFin` totalization of the `j`-th coupling
coordinate is exactly `nzOrderFlat` (its `%` is the identity in range) — reconciling the
generator's `dite`-totalized qubit against `gridFin`'s `Nat.mod_lt` form on `.val` only. -/
theorem gridFin_kindOrderRC_val (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (i : Fin (numStabFormula d)) (j : Nat) (hj : j < nzLenFlat d i.val)
    (rc : Nat × Nat) (hrc : (kindOrderRC d (classifyStab d i.val))[j]? = some rc) :
    (gridFin d hd rc).val = nzOrderFlat d i.val j := by
  have hmem : rc ∈ kindOrderRC d (classifyStab d i.val) := List.mem_of_getElem? hrc
  obtain ⟨h1, h2⟩ := kindOrderRC_classify_in_bounds d hd3 hodd i rc hmem
  have hlt : d * rc.1 + rc.2 < d * d := by
    have h4 : d * (rc.1 + 1) ≤ d * d := by gcongr; omega
    have h5 : d * (rc.1 + 1) = d * rc.1 + d := by ring
    omega
  obtain ⟨rc', hrc', hval⟩ := nzOrderFlat_of_lt d i.val j hj
  rw [hrc] at hrc'
  cases hrc'
  show (d * rc.1 + rc.2) % (d * d) = nzOrderFlat d i.val j
  rw [hval, Nat.mod_eq_of_lt hlt]
  rfl

/-- **Support-Pauli faithfulness at `nzOrderFlat`.**  The code's Pauli at the `j`-th
scheduled qubit is the stabilizer's CSS kind — never `I`/`Y` — so `kindOfPauli` reads it
back as `kindXZ (classifyStab d k)`. -/
theorem surfaceCellPauli_nzOrderFlat (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (i : Fin (numStabFormula d)) (j : Nat) (hj : j < nzLenFlat d i.val) :
    surfaceCellPauli d i.val (nzOrderFlat d i.val j) = kindPauli (classifyStab d i.val) := by
  obtain ⟨rc, hrc, hval⟩ := nzOrderFlat_of_lt d i.val j hj
  have hmem : rc ∈ kindOrderRC d (classifyStab d i.val) := List.mem_of_getElem? hrc
  obtain ⟨h1, h2⟩ := kindOrderRC_classify_in_bounds d hd3 hodd i rc hmem
  have hlt : d * rc.1 + rc.2 < d * d := by
    have h4 : d * (rc.1 + 1) ≤ d * d := by gcongr; omega
    have h5 : d * (rc.1 + 1) = d * rc.1 + d := by ring
    omega
  have hgfval : (gridFin d hd rc).val = nzOrderFlat d i.val j :=
    gridFin_kindOrderRC_val d hd hd3 hodd i j hj rc hrc
  rw [← hgfval, ← mkSurfaceStabilizers_eq_surfaceCellPauli d hd (by omega) i (gridFin d hd rc)]
  show decodeStabPauliAt d i.val ((gridFin d hd rc).val / d) ((gridFin d hd rc).val % d) =
    kindPauli (classifyStab d i.val)
  have hgv : (gridFin d hd rc).val = d * rc.1 + rc.2 := by
    show (d * rc.1 + rc.2) % (d * d) = d * rc.1 + rc.2
    rw [Nat.mod_eq_of_lt hlt]
  rw [hgv]
  have hdiv : (d * rc.1 + rc.2) / d = rc.1 := by
    rw [Nat.mul_add_div hd, Nat.div_eq_of_lt h2]; omega
  have hmod : (d * rc.1 + rc.2) % d = rc.2 := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h2
  rw [hdiv, hmod]
  exact decode_eq_kindPauli_of_mem_kindOrderRC d i.val rc.1 rc.2 (by simpa using hmem)

/-- The `j`-th scheduled qubit index is a genuine data qubit (`< d*d`). -/
theorem nzOrderFlat_lt (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (i : Fin (numStabFormula d)) (j : Nat) (hj : j < nzLenFlat d i.val) :
    nzOrderFlat d i.val j < d * d := by
  obtain ⟨rc, hrc, _⟩ := nzOrderFlat_of_lt d i.val j hj
  rw [← gridFin_kindOrderRC_val d hd hd3 hodd i j hj rc hrc]
  exact (gridFin d hd rc).isLt

/-- **Per-stabilizer schedule equality.**  For odd `d ≥ 3` and any in-range `i`, the
generated schedule at `k = i.val` equals the surface `nzSchedule` — kind by
`surface_evalAt_eq_cellPauli`/`surfaceCellPauli_nzOrderFlat`/`kindOfPauli_kindPauli`,
qubit by `gridFin_kindOrderRC_val` (the `%`-totalization is the identity in range). -/
theorem genSchedule_eq_nzSchedule (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (i : Fin (numStabFormula d)) :
    genSchedule Surface.code nzOrderProg nzLenProg (d * d) d i.val = nzSchedule d hd i := by
  have hpos : 0 < d * d := Nat.mul_pos hd hd
  have hlen : (Term.eval Surface.code.body (CodeFn.fuelForDistance d) nzLenProg
      (Env.code d i.val)).getD 0 = nzLenFlat d i.val := by
    rw [nzLenProg_eval]; rfl
  simp only [genSchedule, hlen, dif_pos hpos, nzSchedule, RuleSchedule.uniform]
  congr 1
  apply List.ext_getElem
  · simp [nzLenFlat_eq]
  · intro j h1 _h2
    have hjlen : j < nzLenFlat d i.val := by
      simpa [List.length_map, List.length_range] using h1
    have horder : (Term.eval Surface.code.body (CodeFn.fuelForDistance d) nzOrderProg
        (Env.cons j (Env.code d i.val))).getD 0 = nzOrderFlat d i.val j := by
      rw [nzOrderProg_eval]; rfl
    simp only [List.getElem_map, List.getElem_range]
    congr 1
    · rw [horder, surface_evalAt_eq_cellPauli d i.val (nzOrderFlat d i.val j) hd3 hodd,
        surfaceCellPauli_nzOrderFlat d hd hd3 hodd i j hjlen, kindOfPauli_kindPauli]
    · apply Fin.ext
      show (Term.eval Surface.code.body (CodeFn.fuelForDistance d) nzOrderProg
        (Env.cons j (Env.code d i.val))).getD 0 % (d * d) = _
      rw [horder, gridFin_kindOrderRC_val d hd hd3 hodd i j hjlen _
        (List.getElem?_eq_getElem (by rw [← nzLenFlat_eq]; exact hjlen))]
      exact Nat.mod_eq_of_lt (nzOrderFlat_lt d hd hd3 hodd i j hjlen)

/-- `List.range n` is the `Fin.val` image of `List.finRange n` — the bridge between the
generator's `List.range numStab` fold and `surfaceXZProgram`'s `List.finRange` fold. -/
private theorem range_eq_finRange_map (n : Nat) :
    List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2; simp

/-- **The re-anchor.**  For odd `d ≥ 3`, the code-blind generator instantiated at
`Surface.code` with the object programs `nzOrderProg` / `nzLenProg` (and `numStab =
d*d - 1`) reproduces the surface compiler-facing program exactly. -/
theorem xzProgramOfPrograms_surface_eq (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    xzProgramOfPrograms Surface.code nzOrderProg nzLenProg (d * d - 1) (d * d) d = surfaceXZProgram d hd := by
  have hcount : d * d - 1 = numStabFormula d := (numStabFormula_eq_sq_sub_one d (by omega)).symm
  unfold xzProgramOfPrograms surfaceXZProgram
  rw [hcount, range_eq_finRange_map, List.foldr_map]
  congr 1
  funext i acc
  rw [genSchedule_eq_nzSchedule d hd hd3 hodd i]

/-- **Corollary (the milestone-S payoff).**  `surfaceCircuit d hd` — definitionally
`compileProgram (surfaceXZProgram d hd)` — is the compilation of the two-object-program
pipeline: substituting the program anchor into any closed headline over
`surfaceCircuit`/`surfaceXZProgram` rephrases it against `xzProgramOfPrograms Surface.code
nzOrderProg nzLenProg (d*d-1) (d*d) d`.

Stated as the well-typed circuit equality after `rw`-ing the program anchor.  (A direct
`surfaceCircuit d hd = compileProgram (xzProgramOfPrograms …)` is *ill-typed* without a
cast: `compileProgram p : FCircuit (n + programHelperCount p)`, so equating the
compilations of two only-propositionally-equal programs would require a `▸`/`HEq`
transport that does not reduce definitionally.  The program anchor
`xzProgramOfPrograms_surface_eq` is the clean, well-typed form and already discharges the
substitution in headlines — one rewrites the *program*, which unifies the dependent
`compileProgram` type automatically.) -/
theorem surfaceCircuit_eq_compileProgram_surface (d : Nat) (hd : 0 < d) (_hd3 : 3 ≤ d)
    (_hodd : d % 2 = 1) :
    surfaceCircuit d hd = compileProgram (surfaceXZProgram d hd) := rfl

/-! ## S2: the scheduled Pauli as one object term

`nzScheduledPauli` computes, in-language, "the Pauli of the `j`-th scheduled coupling"
from *both* object programs at once: the code stabilizer `recCall d k` read at the qubit
selected by the order program `nzOrderProg`. -/

/-- **The NZ scheduled Pauli** (`Term 3 .pauli`): the code's stabilizer `k` (at distance
`d = var 2`, `k = var 1`) evaluated at the `j`-th scheduled qubit `nzOrderProg`. -/
def nzScheduledPauli : Term 3 .pauli :=
  .stabAt (.recCall (.var 2) (.var 1)) nzOrderProg

/-- **Certified evaluation of `nzScheduledPauli`** (odd `d ≥ 3`): the object term evaluates
to the surface cell Pauli at the `j`-th scheduled qubit — composing the `stabAt`/`recCall`
engine (`CodeEvalHelpers.eval_stabAt_recCall`) with `nzOrderProg_eval` and the
`evalEntry?`↔`surfaceCellPauli` bridge. -/
theorem nzScheduledPauli_eval (d k j : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    Term.eval Surface.code.body (d + 2) nzScheduledPauli (Env.cons j (Env.code d k)) =
      some (surfaceCellPauli d k (nzOrderFlat d k j)) := by
  have hdv : Term.eval Surface.code.body (d + 1) (.var 2) (Env.cons j (Env.code d k)) = some d := by
    simp [Term.eval]; rfl
  have hkv : Term.eval Surface.code.body (d + 1) (.var 1) (Env.cons j (Env.code d k)) = some k := by
    simp [Term.eval]; rfl
  have hqv : Term.eval Surface.code.body (d + 2) nzOrderProg (Env.cons j (Env.code d k)) =
      some (nzOrderFlat d k j) := nzOrderProg_eval Surface.code.body (d + 2) d k j
  rw [nzScheduledPauli, CodeEvalHelpers.eval_stabAt_recCall Surface.code hdv hkv hqv]
  have hev := evalEntry_surfaceCellPauli (oddDist d) k (nzOrderFlat d k j)
  rw [oddDist_distance d hd3 hodd] at hev
  exact hev

/-! ## S4b (payoff): the generated schedule satisfies the NZ spec

Composing S3b's `genSchedule_eq_nzSchedule` with `nzSchedule_isNZScheduleOf`, the schedule
*produced by the two object programs* is the NZ schedule of `Surface.code`'s content —
the spec now speaks about the two-program pipeline's output directly. -/
theorem genSchedule_isNZScheduleOf (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (i : Fin (numStabFormula d)) :
    IsNZScheduleOf d (surfaceCellPauli d i.val)
      (genSchedule Surface.code nzOrderProg nzLenProg (d * d) d i.val) := by
  rw [genSchedule_eq_nzSchedule d hd hd3 hodd i]
  exact nzSchedule_isNZScheduleOf d hd hd3 hodd i

end QStab.QClifford.Compile
