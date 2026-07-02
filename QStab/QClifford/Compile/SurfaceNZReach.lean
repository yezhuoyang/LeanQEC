import QStab.QClifford.Compile.SurfaceNZStabTransport

/-!
# F2 reach: the domino-path attack script (generator + sanity)

The reach `VCSlot` asks for a fault script `reachScript : List (Option Pauli)` such that a
clean-start run of the compiled Surface/NZ circuit fires exactly `d` faults and lands in a
`failure` state (a logical residual with all detectors/flags zero).

This file builds that script — the **domino-path** placement — and validates its arithmetic
by `#eval` at small `d` *before* any proof (per the F2 plan).  The per-gadget `runFScript`
lemma family and the through-`compileProgramAux` induction are layered on top downstream.

## The design (fixed; see the F2 handover)

Column 0 of the rotated code is qubits `(r,0)` = row-major index `d*r`.  The logical `X̄` is
the full column-0 `X`-string; `Z̄ = mkSurfaceLogicalZ` is the row-0 `Z`-string; they overlap
once, so `X̄` anticommutes with `Z̄` (barZ membership).

Injections (`d` total): for each column-0 bulk `Z`-check `bulkZ(r,0)` (necessarily `r` even,
`r ≤ d-3`), inject `X` on `(r,0)` and `(r+1,0)` at their coupling sites (slot-0/slot-1 data
errLocs, offsets `1,3`) — the ancilla receives `X` twice, cancelling its detector.  For the
last row `(d-1,0)`, inject `X` inside the `X`-check `bulkX(d-2,0)` at the slot-2 before-`H₁`
site (offset `9`) — `H`-conjugation keeps the ancilla clean.  The even dominoes `{r,r+1}`
tile rows `0..d-2`; the last injection adds row `d-1`; union = full column 0 = `X̄`.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.QClifford.PCC.SurfaceNZ
open QStab.Examples.SurfaceParametric

/-- errLoc sites contributed by one schedule slot: a `Z` slot is a bare `CNOT` (2 sites),
an `X` slot is `H ; CNOT ; H` (4 sites). -/
def slotSiteCount : XZPauli → Nat
  | .Z => 2
  | .X => 4

/-- Total errLoc count of gadget `k`'s compiled NZ block:
`prep0` (1) + `Σ slots` + `flagMeasZ` (1). -/
def gadgetErrLocCount (d : Nat) (k : Nat) : Nat :=
  let kind := classifyStab d k
  2 + (kindOrderRC d kind).length * slotSiteCount (kindXZ kind)

/-- The per-gadget reach segment (domino-path injections).  Length is exactly the gadget's
errLoc count, so segments concatenate into a well-aligned flat script. -/
def surfaceReachSegment (d : Nat) (k : Nat) : List (Option Pauli) :=
  let len := gadgetErrLocCount d k
  match classifyStab d k with
  | .bulkZ _ 0 =>
      -- even domino: X at the slot-0 and slot-1 data-coupling sites
      (List.range len).map (fun o => if o = 1 ∨ o = 3 then some Pauli.X else none)
  | .bulkX r 0 =>
      if r + 2 = d then
        -- last row: X at the slot-2 before-H₁ site (offset 1 + 2*4)
        (List.range len).map (fun o => if o = 9 then some Pauli.X else none)
      else
        List.replicate len none
  | _ => List.replicate len none

/-- **The domino-path reach script** for `compileProgram (surfaceXZProgram d hd)`:
the per-gadget segments in measurement (index) order. -/
def surfaceReachScript (d : Nat) (_hd : 0 < d) : List (Option Pauli) :=
  ((List.finRange (numStabFormula d)).map (fun k => surfaceReachSegment d k.val)).flatten

/-! ## Reusable machinery: `runFScript` composition over gadget blocks

The compiled program is a concatenation of gadget blocks; the reach proof decomposes the run
gadget-by-gadget.  `runFScript_append` is the composition law: running `fc1 ++ fc2` splits the
script at `fc1`'s errLoc count.  (`runFScript`/`runFScript_sound` live in the protected
Basic.lean — consumed here, never edited.) -/

/-- Number of `errLoc` sites in a fault circuit = number of script entries it consumes. -/
def errLocCount {nq : Nat} : FCircuit nq → Nat
  | [] => 0
  | .gate _ :: rest => errLocCount rest
  | .errLoc _ :: rest => errLocCount rest + 1

/-- **`runFScript` composition law** (unconditional).  Running `fc1 ++ fc2` runs `fc1` on the
script prefix, then `fc2` on `script.drop (errLocCount fc1)`; counts add.  No length side
condition: if the script is exhausted inside `fc1`, its trailing errLocs are no-ops
(`Basic.lean:501`) and `List.drop n [] = []` keeps both sides aligned. -/
theorem runFScript_append {nq : Nat} :
    ∀ (fc1 fc2 : FCircuit nq) (script : List (Option Pauli)) (es : ErrorState nq),
      runFScript (fc1 ++ fc2) script es =
        ((runFScript fc2 (script.drop (errLocCount fc1)) (runFScript fc1 script es).1).1,
         (runFScript fc1 script es).2 +
           (runFScript fc2 (script.drop (errLocCount fc1)) (runFScript fc1 script es).1).2) := by
  intro fc1
  induction fc1 with
  | nil =>
      intro fc2 script es
      simp [runFScript, errLocCount]
  | cons ev rest ih =>
      intro fc2 script es
      cases ev with
      | gate g =>
          show runFScript (rest ++ fc2) script (propagateGate g es) = _
          rw [ih fc2 script (propagateGate g es)]
          simp [runFScript, errLocCount]
      | errLoc q =>
          cases script with
          | nil =>
              show runFScript (rest ++ fc2) [] es = _
              rw [ih fc2 [] es]
              simp [runFScript, errLocCount, List.drop_nil]
          | cons o script' =>
              cases o with
              | none =>
                  show runFScript (rest ++ fc2) script' es = _
                  rw [ih fc2 script' es]
                  simp [runFScript, errLocCount]
              | some p =>
                  by_cases hp : p = Pauli.I
                  · subst hp
                    show runFScript (rest ++ fc2) script' es = _
                    rw [ih fc2 script' es]
                    simp [runFScript, errLocCount]
                  · rw [List.cons_append]
                    simp only [runFScript, if_neg hp]
                    rw [ih fc2 script' (es.inject q p)]
                    simp only [errLocCount, List.drop_succ_cons]
                    congr 1
                    omega
/-- errLoc counts add over circuit concatenation (Step-1c arithmetic suite). -/
@[simp] theorem errLocCount_append {nq : Nat} (fc1 fc2 : FCircuit nq) :
    errLocCount (fc1 ++ fc2) = errLocCount fc1 + errLocCount fc2 := by
  induction fc1 with
  | nil => simp [errLocCount]
  | cons ev rest ih =>
      cases ev with
      | gate g => simpa [errLocCount] using ih
      | errLoc q => simp only [List.cons_append, errLocCount, ih]; omega

/-! ## Sanity `#eval`s (design-arithmetic validation, pre-proof) -/

/-- Number of injected (non-`none`) faults in the script. -/
def scriptFaultCount (s : List (Option Pauli)) : Nat :=
  (s.filter (fun o => o.isSome)).length

-- Fault count must equal `d`.
#eval scriptFaultCount (surfaceReachScript 3 (by decide))   -- expect 3
#eval scriptFaultCount (surfaceReachScript 5 (by decide))   -- expect 5
#eval scriptFaultCount (surfaceReachScript 7 (by decide))   -- expect 7

-- The actual run: fault count `.2` and the data residual `.1`.
#eval (runFScript (compileProgram (surfaceXZProgram 3 (by decide)))
        (surfaceReachScript 3 (by decide)) (ErrorState.clean _)).2   -- expect 3

-- Data residual should be X on column 0 (indices 0, 3, 6 for d=3), I elsewhere.
#eval ((List.finRange 9).map (fun q =>
        (runFScript (compileProgram (surfaceXZProgram 3 (by decide)))
          (surfaceReachScript 3 (by decide)) (ErrorState.clean _)).1.paulis
          (Fin.castAdd _ q)))
      -- expect [X,I,I, X,I,I, X,I,I]

-- d=5 data residual: X on column 0 (indices 0,5,10,15,20), I elsewhere.
#eval ((List.finRange 25).map (fun q =>
        (runFScript (compileProgram (surfaceXZProgram 5 (by decide)))
          (surfaceReachScript 5 (by decide)) (ErrorState.clean _)).1.paulis
          (Fin.castAdd _ q)))

-- ★ THE DETECTOR CHECK (the trap the domino design avoids): every flag/detector zero.
#eval decide (allFlagsZero
        (fullProgramCodeSpecD (surfaceXZProgram 3 (by decide))
          (fullProgramReadoutDisjoint_auto _) 3 (by decide))
        (runFScript (compileProgram (surfaceXZProgram 3 (by decide)))
          (surfaceReachScript 3 (by decide)) (ErrorState.clean _)).1)   -- expect true
#eval decide (allFlagsZero
        (fullProgramCodeSpecD (surfaceXZProgram 5 (by decide))
          (fullProgramReadoutDisjoint_auto _) 5 (by decide))
        (runFScript (compileProgram (surfaceXZProgram 5 (by decide)))
          (surfaceReachScript 5 (by decide)) (ErrorState.clean _)).1)   -- expect true

end QStab.QClifford.Compile
