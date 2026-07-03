import QStab.QClifford.Compile.SurfaceNZStabTransport
import QStab.QClifford.Compile.NZReachCalculus

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

/-! ## (a) Script decode — surface segment as a generic `blockScript` -/

/-- The per-gadget injection pattern (one `Bool` per schedule slot), pinned per
`classifyStab` kind: column-0 bulk `Z`-checks inject their two column-0 data slots; the
last-row `X`-check injects its slot-2 before-H₁ site; everything else is fault-free. -/
def injs_k (d k : Nat) : List Bool :=
  match classifyStab d k with
  | .bulkZ _ 0 => [true, true, false, false]
  | .bulkZ _ _ => [false, false, false, false]
  | .bulkX r 0 => if r + 2 = d then [false, false, true, false] else [false, false, false, false]
  | .bulkX _ _ => [false, false, false, false]
  | .topX _ => [false, false]
  | .rightZ _ => [false, false]
  | .leftZ _ => [false, false]
  | .bottomX _ => [false, false]

/-- **Decode, `bulkZ(_,0)` case.**  The offset-based surface segment equals the generic
`blockScript` over the (4 `Z`-kind) lifted slots with the domino injection pattern. -/
theorem surfaceReachSegment_decode_bulkZ (d : Nat) (hd : 0 < d) (total : Nat)
    (k : Fin (numStabFormula d)) (r : Nat) (h : classifyStab d k.val = .bulkZ r 0) :
    surfaceReachSegment d k.val
      = blockScript (liftSchedule (k := total) (nzSchedule d hd k)).slots (injs_k d k.val) := by
  simp only [surfaceReachSegment, gadgetErrLocCount, injs_k, h, kindXZ, slotSiteCount,
    kindOrderRC, nzSchedule, liftSchedule, RuleSchedule.uniform, blockScript, slotsScript,
    slotScript, liftSlot, List.map_cons, List.map_nil, List.headD_cons, List.tail_cons]
  rfl

/-- **Decode, `bulkX(d-2,0)` case** (the last-row injector, 4 `X`-kind slots). -/
theorem surfaceReachSegment_decode_bulkX_last (d : Nat) (hd : 0 < d) (total : Nat)
    (k : Fin (numStabFormula d)) (r : Nat) (h : classifyStab d k.val = .bulkX r 0)
    (hr : r + 2 = d) :
    surfaceReachSegment d k.val
      = blockScript (liftSchedule (k := total) (nzSchedule d hd k)).slots (injs_k d k.val) := by
  simp only [surfaceReachSegment, gadgetErrLocCount, injs_k, h, hr, if_true, kindXZ,
    slotSiteCount, kindOrderRC, nzSchedule, liftSchedule, RuleSchedule.uniform, blockScript,
    slotsScript, slotScript, liftSlot, List.map_cons, List.map_nil, List.headD_cons,
    List.tail_cons]
  rfl

/-- **Decode, fault-free bulk `Z`(c≥1).** -/
theorem surfaceReachSegment_decode_bulkZ_col (d : Nat) (hd : 0 < d) (total : Nat)
    (k : Fin (numStabFormula d)) (r c : Nat) (h : classifyStab d k.val = .bulkZ r (c + 1)) :
    surfaceReachSegment d k.val
      = blockScript (liftSchedule (k := total) (nzSchedule d hd k)).slots (injs_k d k.val) := by
  simp only [surfaceReachSegment, gadgetErrLocCount, injs_k, h, kindXZ, slotSiteCount,
    kindOrderRC, nzSchedule, liftSchedule, RuleSchedule.uniform, blockScript, slotsScript,
    slotScript, liftSlot, List.map_cons, List.map_nil, List.headD_cons, List.tail_cons]
  rfl

/-- **Decode, non-last bulk `X`(_,0).** -/
theorem surfaceReachSegment_decode_bulkX_off (d : Nat) (hd : 0 < d) (total : Nat)
    (k : Fin (numStabFormula d)) (r : Nat) (h : classifyStab d k.val = .bulkX r 0)
    (hr : ¬ (r + 2 = d)) :
    surfaceReachSegment d k.val
      = blockScript (liftSchedule (k := total) (nzSchedule d hd k)).slots (injs_k d k.val) := by
  simp only [surfaceReachSegment, gadgetErrLocCount, injs_k, h, if_neg hr, kindXZ, slotSiteCount,
    kindOrderRC, nzSchedule, liftSchedule, RuleSchedule.uniform, blockScript, slotsScript,
    slotScript, liftSlot, List.map_cons, List.map_nil, List.headD_cons, List.tail_cons]
  rfl

/-- **Decode, bulk `X`(c≥1).** -/
theorem surfaceReachSegment_decode_bulkX_col (d : Nat) (hd : 0 < d) (total : Nat)
    (k : Fin (numStabFormula d)) (r c : Nat) (h : classifyStab d k.val = .bulkX r (c + 1)) :
    surfaceReachSegment d k.val
      = blockScript (liftSchedule (k := total) (nzSchedule d hd k)).slots (injs_k d k.val) := by
  simp only [surfaceReachSegment, gadgetErrLocCount, injs_k, h, kindXZ, slotSiteCount,
    kindOrderRC, nzSchedule, liftSchedule, RuleSchedule.uniform, blockScript, slotsScript,
    slotScript, liftSlot, List.map_cons, List.map_nil, List.headD_cons, List.tail_cons]
  rfl

/-- **Decode, boundary kinds** (topX / rightZ / leftZ / bottomX — 2 slots, fault-free). -/
theorem surfaceReachSegment_decode_topX (d : Nat) (hd : 0 < d) (total : Nat)
    (k : Fin (numStabFormula d)) (b : Nat) (h : classifyStab d k.val = .topX b) :
    surfaceReachSegment d k.val
      = blockScript (liftSchedule (k := total) (nzSchedule d hd k)).slots (injs_k d k.val) := by
  simp only [surfaceReachSegment, gadgetErrLocCount, injs_k, h, kindXZ, slotSiteCount,
    kindOrderRC, nzSchedule, liftSchedule, RuleSchedule.uniform, blockScript, slotsScript,
    slotScript, liftSlot, List.map_cons, List.map_nil, List.headD_cons, List.tail_cons]
  rfl

theorem surfaceReachSegment_decode_rightZ (d : Nat) (hd : 0 < d) (total : Nat)
    (k : Fin (numStabFormula d)) (b : Nat) (h : classifyStab d k.val = .rightZ b) :
    surfaceReachSegment d k.val
      = blockScript (liftSchedule (k := total) (nzSchedule d hd k)).slots (injs_k d k.val) := by
  simp only [surfaceReachSegment, gadgetErrLocCount, injs_k, h, kindXZ, slotSiteCount,
    kindOrderRC, nzSchedule, liftSchedule, RuleSchedule.uniform, blockScript, slotsScript,
    slotScript, liftSlot, List.map_cons, List.map_nil, List.headD_cons, List.tail_cons]
  rfl

theorem surfaceReachSegment_decode_leftZ (d : Nat) (hd : 0 < d) (total : Nat)
    (k : Fin (numStabFormula d)) (b : Nat) (h : classifyStab d k.val = .leftZ b) :
    surfaceReachSegment d k.val
      = blockScript (liftSchedule (k := total) (nzSchedule d hd k)).slots (injs_k d k.val) := by
  simp only [surfaceReachSegment, gadgetErrLocCount, injs_k, h, kindXZ, slotSiteCount,
    kindOrderRC, nzSchedule, liftSchedule, RuleSchedule.uniform, blockScript, slotsScript,
    slotScript, liftSlot, List.map_cons, List.map_nil, List.headD_cons, List.tail_cons]
  rfl

theorem surfaceReachSegment_decode_bottomX (d : Nat) (hd : 0 < d) (total : Nat)
    (k : Fin (numStabFormula d)) (b : Nat) (h : classifyStab d k.val = .bottomX b) :
    surfaceReachSegment d k.val
      = blockScript (liftSchedule (k := total) (nzSchedule d hd k)).slots (injs_k d k.val) := by
  simp only [surfaceReachSegment, gadgetErrLocCount, injs_k, h, kindXZ, slotSiteCount,
    kindOrderRC, nzSchedule, liftSchedule, RuleSchedule.uniform, blockScript, slotsScript,
    slotScript, liftSlot, List.map_cons, List.map_nil, List.headD_cons, List.tail_cons]
  rfl

/-- Count equality: the surface segment's length is `gadgetErrLocCount d k`. -/
theorem surfaceReachSegment_length (d k : Nat) :
    (surfaceReachSegment d k).length = gadgetErrLocCount d k := by
  unfold surfaceReachSegment
  split
  all_goals first
    | (split_ifs <;> simp [List.length_map, List.length_range, List.length_replicate])
    | simp [List.length_map, List.length_range, List.length_replicate]

/-! ## Sanity `#eval`s (design-arithmetic validation, pre-proof)

(`errLocCount`, `runFScript_append`, `errLocCount_append` now live in the surface-free
`NZReachCalculus`; imported above.) -/

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
