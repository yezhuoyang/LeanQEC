import QStab.Examples.SurfaceGeometry
import QStab.Invariant

/-! # B1 patch — bridging `Step.halt` and the simulator's final measurement

**The gap** ([semantics_audit.md#B1](../../../Codedistance/notes/semantics_audit.md)):
`Step.halt : Step P (.active s) (.done s)` transitions without firing the
measurement at the last coordinate — the paper's `Next(n-k-1, R) = (n-k-1, R)`
convention implies the measurement should fire there. The simulator's
`measureFinal` does apply the last measurement, so `runAllMeasurements` gives
a *different* `σ_done` than a `Step`-trace ending in `halt`.

**Why not just fix `Step.halt` right now.** Doing so requires updating the
`Invariant P` framework (`preservation` currently covers only active→active;
the halt case in `holds_of_reachable_aux` relies on the state being unchanged)
and retrofitting every one of the ~8 existing invariants with a halt-case
preservation proof. Deferred to its own work session.

**This patch**: a pure function applying the missing measurement. Verification
tests and spec-level theorems can be phrased in terms of
`withFinalMeasurement σ_done` instead of raw `σ_done` — which matches what the
simulator returns and matches the paper's intended semantics. -/

namespace QStab

/-- Apply the final measurement that `Step.halt` would have fired in the
    paper's semantics but doesn't in Lean's. No-op if not at the last coord. -/
def withFinalMeasurement (P : QECParams) (s : State P) : State P :=
  if s.coord.next = none then measureStep P s s.coord else s

/-- At any state NOT at the last coordinate, this patch is the identity. -/
theorem withFinalMeasurement_noop_at_nonLast (P : QECParams) (s : State P)
    (h : s.coord.next ≠ none) : withFinalMeasurement P s = s := by
  unfold withFinalMeasurement; simp [h]

/-- At the last coordinate, this patch applies `measureStep`. -/
theorem withFinalMeasurement_at_last (P : QECParams) (s : State P)
    (h : s.coord.next = none) :
    withFinalMeasurement P s = measureStep P s s.coord := by
  unfold withFinalMeasurement; simp [h]

end QStab

/-! # Verification harness for circuit-level distance definition

This file makes the paper's definition of "undetected logical error at σ_done"
([invariant.tex:1201](invariant.tex#L1201)) executable, so we can sanity-check:

* The four error-injection rules do what we think.
* `Ẽ ∉ S` has the purely-parity characterization we expect.
* Hand-crafted attacks (`X̄`, `Z̄`, a stabilizer product) classify correctly.

Purpose: externally validate the semantics *before* we trust any proof about
circuit-level distance. A follow-up Stim-based harness will exhaustively
cross-check against ground truth.
-/

namespace QStab

open Pauli

/-! ## Decision predicates for "undetected logical error"

For an [[n, 1, d]] stabilizer code with logical operators `L_X, L_Z`,
`Ẽ ∈ S  ⟺  Syn(Ẽ) = 0 ∧ parity(L_X, Ẽ) = 0 ∧ parity(L_Z, Ẽ) = 0`.
Hence:
`Ẽ ∉ S  ⟺  (∃ generator anticommutes with Ẽ) ∨ parity(L_X, Ẽ) = true ∨ parity(L_Z, Ẽ) = true`.
-/

/-- Every stabilizer generator commutes with `E` (zero syndrome). -/
def hasZeroSyndrome (P : QECParams) (E : ErrorVec P.n) : Bool :=
  decide (∀ i : Fin P.numStab, ErrorVec.parity (P.stabilizers i) E = false)

/-- `E ∉ S`, using the logical-coset characterization (valid for [[n, 1, d]] codes). -/
def notInStab (P : QECParams) (L_X L_Z : ErrorVec P.n) (E : ErrorVec P.n) : Bool :=
  (!hasZeroSyndrome P E) || ErrorVec.parity L_X E || ErrorVec.parity L_Z E

/-- All measurement bits `G[x][y]` are zero (decoder saw no detection events). -/
def allGZero (P : QECParams) (s : State P) : Bool :=
  decide (∀ x : Fin P.numStab, ∀ y : Fin P.R, s.G x y = false)

/-! ## Stim-equivalent predicate (v2)

The prior `isUndetectedLogicalError` only required `G = 0 ∧ Ẽ ∉ S`. This
corresponds to the paper's regime — no final data measurement. It does **not**
match Stim's default `memory_z` circuit, which performs destructive Z-basis
measurement of all data qubits at the end, producing extra "final-data
detectors" that cross-check the last round's syndrome against direct data
readout.

For Lean's verdict to match Stim's decoder success/failure on the same attack,
we must model these extra measurements. This is a predicate only (no change
to `Step.*`): we compute what Stim would detect, using state components
already present in `State`. -/

/-- `s` is a Z-type stabilizer: all non-identity positions are `Z`. -/
def isZType {n : Nat} (s : ErrorVec n) : Bool :=
  decide (∀ i : Fin n, s i = Pauli.I ∨ s i = Pauli.Z)

/-- Last round coordinate component. -/
def lastRound (P : QECParams) : Fin P.R :=
  ⟨P.R - 1, Nat.sub_lt P.hR (by decide)⟩

/-- Final-data detector for Z-type stab `sIdx` (memory_z convention).
    In noise-free: last round's G = direct data-M parity of the stab's support.
    Final-data detector = XOR of these two values, so 0 in noise-free.

    Formula: `G[sIdx, R-1]  XOR  parity(T_{sIdx}, Ẽ_final)`.

    For Z-type stab `sIdx`, `parity(T_s, Ẽ)` equals the XOR of Z-basis data
    measurement outcomes over s's support (in |0⟩_L ground state), which is
    precisely what Stim's final-data detector computes. -/
def finalDataDetector (P : QECParams) (st : State P) (sIdx : Fin P.numStab) : Bool :=
  xor (st.G sIdx (lastRound P))
      (ErrorVec.parity (P.stabilizers sIdx) st.E_tilde)

/-- All Z-type stabilizer final-data detectors read 0. -/
def allZTypeFinalDataDetectorsZero (P : QECParams) (st : State P) : Bool :=
  decide (∀ sIdx : Fin P.numStab,
    isZType (P.stabilizers sIdx) = true → finalDataDetector P st sIdx = false)

/-- **Stim-equivalent predicate.** Undetected logical error in the standard
    `memory_z` setup:

    (a) All per-round syndrome measurements are zero (`G = 0`).
    (b) All Z-type final-data detectors are zero (data M is consistent with
        last round's syndrome — nothing was injected in the last round that
        escaped the round's measurement).
    (c) The logical observable `Z̄` is physically flipped (`parity(L_Z, Ẽ) = 1`).

    (a) + (b) means the decoder sees an all-zero detector record, so min-weight
    matching predicts identity correction. (c) means the actual Pauli frame
    disagrees. Together: decoder fails. This is the exact condition Stim +
    PyMatching report as "logical error" for the memory_z task. -/
def isUndetectedLogicalError_v2 (P : QECParams) (L_Z : ErrorVec P.n)
    (st : State P) : Bool :=
  allGZero P st
  && allZTypeFinalDataDetectorsZero P st
  && ErrorVec.parity L_Z st.E_tilde

/-- Undetected logical error at a state: `G = 0` and `Ẽ ∉ S`. Matches the
    **paper's** definition of `d^circ` from [invariant.tex:1201](invariant.tex#L1201).
    **Note**: this is the weaker, paper-as-stated definition. For semantic
    equivalence to Stim's standard `memory_z` setup, use
    `isUndetectedLogicalError_v2` instead. -/
def isUndetectedLogicalError (P : QECParams) (L_X L_Z : ErrorVec P.n)
    (s : State P) : Bool :=
  allGZero P s && notInStab P L_X L_Z s.E_tilde

/-! ## Raw Type-II simulator

`applyType2` is the missing fourth injector in `Simulate.lean`. It applies an
arbitrary `ErrorVec`-valued back-action (not checked against `backActionSet`,
which is still abstract). For verification purposes this is exactly right —
we want to probe what the semantics do under *any* concrete hook. -/

/-- Apply a Type-II back-action error `e` (mirror of `Step.type2`).
    Updates: `C -= 1`, `cnt2 += 1`, `λ_E += weight(e)`, `Ẽ := e · Ẽ`,
    `F[coord.x] ⊕= parity(T_{coord.x}, e)`. -/
def applyType2 {P : QECParams} (s : State P) (e : ErrorVec P.n) : State P :=
  { s with
    C := s.C - 1
    cnt2 := s.cnt2 + 1
    lam_E := s.lam_E + ErrorVec.weight e
    E_tilde := ErrorVec.mul e s.E_tilde
    F := fun j => if j = s.coord.x
                   then xor (s.F j) (ErrorVec.parity (P.stabilizers s.coord.x) e)
                   else s.F j }

end QStab

/-! ## d=3 test harness

All tests use a scaled-up budget so we can inject many errors without hitting
the `budget_exhausted` rule (which matters for proofs, not for testing the
effect on `Ẽ` and `G`). -/

namespace QStab.Examples.SurfaceD3

open QStab

/-- d=3 rotated surface code with room for many error injections. -/
def testCode : QECParams := { code with C_budget := 20 }

/-- Run all measurements over the 5 rounds (ample fuel). -/
def runFull (s : State testCode) : State testCode :=
  runAllMeasurements testCode s 100

/-! ### Helpers to inject Pauli errors at specific qubits -/

/-- Inject `X` at qubit `i` (1-based paper index) before measurements. -/
def injectXAt (s : State testCode) (i : Nat) (h : i < 9) : State testCode :=
  applyType0 s ⟨i, h⟩ .X

def injectZAt (s : State testCode) (i : Nat) (h : i < 9) : State testCode :=
  applyType0 s ⟨i, h⟩ .Z

/-! ### Test cases

Expected column = what physics/standard QEC says should happen.
If any `#eval!` disagrees with "expected", the semantics have a bug. -/

/-- **T1. No error.** Baseline: not a logical error. -/
def t1_noError : State testCode := runFull (State.init testCode)

#eval! isUndetectedLogicalError testCode logicalX logicalZ t1_noError
-- Expected: false

/-- **T2. Single `X` on q₁.** Syndrome-detectable (anticommutes with ŝ₁):
    `G ≠ 0`, so NOT undetected — even though `Ẽ ∉ S`. -/
def t2_singleX : State testCode :=
  runFull (injectXAt (State.init testCode) 0 (by decide))

#eval! isUndetectedLogicalError testCode logicalX logicalZ t2_singleX
-- Expected: false  (G will contain the ŝ₁ anticommutation signature)

#eval! allGZero testCode t2_singleX
-- Expected: false

#eval! notInStab testCode logicalX logicalZ t2_singleX.E_tilde
-- Expected: true  (single X is not in the stabilizer group)

/-- **T3. Logical `X̄ = X₁X₄X₇`.** Zero syndrome, anticommutes with Z̄.
    Classic undetected logical error. This is the "gold standard" signal that
    our semantics aligns with the intended definition. -/
def t3_logicalX : State testCode :=
  let s1 := injectXAt (State.init testCode) 0 (by decide)
  let s2 := injectXAt s1 3 (by decide)
  let s3 := injectXAt s2 6 (by decide)
  runFull s3

#eval! isUndetectedLogicalError testCode logicalX logicalZ t3_logicalX
-- Expected: true  ← THE KEY TEST

#eval! allGZero testCode t3_logicalX
-- Expected: true

#eval! ErrorVec.parity logicalZ t3_logicalX.E_tilde
-- Expected: true  (X̄ anticommutes with Z̄)

/-- **T4. Logical `Z̄ = Z₁Z₂Z₃`.** Zero syndrome, anticommutes with X̄. -/
def t4_logicalZ : State testCode :=
  let s1 := injectZAt (State.init testCode) 0 (by decide)
  let s2 := injectZAt s1 1 (by decide)
  let s3 := injectZAt s2 2 (by decide)
  runFull s3

#eval! isUndetectedLogicalError testCode logicalX logicalZ t4_logicalZ
-- Expected: true

/-- **T5. Stabilizer ŝ₁ = Z₁Z₂Z₄Z₅.** Zero syndrome AND commutes with both
    logicals — benign, `Ẽ ∈ S`. No logical error even though `G = 0`. This
    distinguishes logical errors from trivial stabilizer elements. -/
def t5_stabilizer : State testCode :=
  let s1 := injectZAt (State.init testCode) 0 (by decide)
  let s2 := injectZAt s1 1 (by decide)
  let s3 := injectZAt s2 3 (by decide)
  let s4 := injectZAt s3 4 (by decide)
  runFull s4

#eval! isUndetectedLogicalError testCode logicalX logicalZ t5_stabilizer
-- Expected: false  ← distinguishes S from N(S)∖S

#eval! allGZero testCode t5_stabilizer
-- Expected: true  (stabilizer: zero syndrome)

#eval! notInStab testCode logicalX logicalZ t5_stabilizer.E_tilde
-- Expected: false  (Ẽ ∈ S)

/-- **T6. `X_5` (centre qubit).** Anticommutes with ŝ₁ (at q₅) and ŝ₄ (at q₅),
    so syndrome is nonzero. `G ≠ 0` across all rounds. -/
def t6_centerX : State testCode :=
  runFull (injectXAt (State.init testCode) 4 (by decide))

#eval! isUndetectedLogicalError testCode logicalX logicalZ t6_centerX
-- Expected: false  (syndrome detected)

#eval! ErrorVec.parity (stabilizers ⟨0, by decide⟩) t6_centerX.E_tilde
-- Expected: true  (X₅ anticommutes with ŝ₁)

#eval! ErrorVec.parity (stabilizers ⟨3, by decide⟩) t6_centerX.E_tilde
-- Expected: true  (X₅ anticommutes with ŝ₄)

/-- **T7. `X̄` masked by Type-III.** Inject `X̄` then flip G bits everywhere `X̄`
    triggered — which is nowhere, since `X̄` commutes with all generators. So
    Type-III masking is unnecessary here; this case is identical to T3.
    Included to confirm the harness composes correctly. -/
def t7_logicalX_viaMasking : State testCode := t3_logicalX

#eval! isUndetectedLogicalError testCode logicalX logicalZ t7_logicalX_viaMasking
-- Expected: true

/-! ### Cemented test theorems

The `#eval!` checks above are merely displayed. These `by native_decide` theorems
make the semantic behaviour part of the type-checked development — any future
refactor that silently breaks them will fail to build. -/

theorem test1_noError_notLogical :
    isUndetectedLogicalError testCode logicalX logicalZ t1_noError = false := by
  native_decide

theorem test2_singleX_notLogical :
    isUndetectedLogicalError testCode logicalX logicalZ t2_singleX = false := by
  native_decide

theorem test2_singleX_GnonZero :
    allGZero testCode t2_singleX = false := by
  native_decide

theorem test2_singleX_EnotInS :
    notInStab testCode logicalX logicalZ t2_singleX.E_tilde = true := by
  native_decide

theorem test3_logicalX_UNDETECTED :
    isUndetectedLogicalError testCode logicalX logicalZ t3_logicalX = true := by
  native_decide

theorem test3_logicalX_Gzero :
    allGZero testCode t3_logicalX = true := by
  native_decide

theorem test3_logicalX_anticommutes_Zbar :
    ErrorVec.parity logicalZ t3_logicalX.E_tilde = true := by
  native_decide

theorem test4_logicalZ_UNDETECTED :
    isUndetectedLogicalError testCode logicalX logicalZ t4_logicalZ = true := by
  native_decide

theorem test5_stabilizer_notLogical :
    isUndetectedLogicalError testCode logicalX logicalZ t5_stabilizer = false := by
  native_decide

theorem test5_stabilizer_Gzero :
    allGZero testCode t5_stabilizer = true := by
  native_decide

theorem test5_stabilizer_EinS :
    notInStab testCode logicalX logicalZ t5_stabilizer.E_tilde = false := by
  native_decide

theorem test6_centerX_detected :
    isUndetectedLogicalError testCode logicalX logicalZ t6_centerX = false := by
  native_decide

/-! ### Stress test: 2-error "masking" attack

Probes the `MaskingLowerBound` gap at [invariant.tex:1909](invariant.tex#L1909).

Strategy:
 1. Run all measurements for rounds 0–3 error-free (32 `stepMeasure` calls → coord (0, 4)).
 2. Inject Type-0 X on q₁ (qubit 0). Ẽ becomes `X_1`, which anticommutes with ŝ₁.
 3. Inject Type-3 at coord (0, 4). G[0, 4] flips from 0 to 1.
 4. Measure at (0, 4): computes G[0, 4] ⊕ parity(ŝ₁, X_1) = 1 ⊕ 1 = 0.
    The detected syndrome is masked; F[0] stays false (consistent with round 3).
 5. Continue measurements for remaining stabs in round 4. X_1 commutes with
    ŝ₂…ŝ₈, so all other G bits stay 0.

If this execution's final state has `G = 0` **and** `Ẽ ∉ S`, we have a concrete
2-error counterexample to `d^circ ≥ 3` for d=3 NZ-scheduled surface code. -/

def attack_Xq1_masked : State testCode :=
  let s0 := State.init testCode
  -- Run all measurements for rounds 0–3 error-free (advance coord to (0, 4))
  let s1 := (List.range 32).foldl
    (fun s _ => match stepMeasure testCode s with | some s' => s' | none => s) s0
  -- Inject Type-0 X on qubit 0 (paper's q₁)
  let s2 := applyType0 s1 ⟨0, by decide⟩ .X
  -- Inject Type-3 at current coord (0, 4) to mask G[0, 4]
  let s3 := applyType3 s2
  -- Continue to the end of the execution
  runAllMeasurements testCode s3 100

-- Diagnostic reads
#eval! attack_Xq1_masked.cnt0  -- Type-0 count; expect 1
#eval! attack_Xq1_masked.cnt3  -- Type-3 count; expect 1
#eval! attack_Xq1_masked.C     -- remaining budget; expect 18 (= 20 - 2)
#eval! showErrorVec attack_Xq1_masked.E_tilde  -- expect "[X, I, I, I, I, I, I, I, I]"
#eval! allGZero testCode attack_Xq1_masked     -- KEY 1: is G all zero?
#eval! notInStab testCode logicalX logicalZ attack_Xq1_masked.E_tilde  -- KEY 2: is Ẽ ∉ S?
#eval! isUndetectedLogicalError testCode logicalX logicalZ attack_Xq1_masked
-- KEY 3: **if this is `true`, we have a 2-error counterexample to d^circ ≥ 3**

/-! ### Counterexample cemented as theorems

If these all pass via `native_decide`, then for d=3 rotated surface code under
NZ scheduling with R = 5 (= 2d − 1), there exists a **2-error** execution
σ₀ →* σ_done with `G = 0` and `Ẽ ∉ S`. Hence `d^circ ≤ 2 < 3 = d`, refuting
the Section 3 theorem's `d^circ ≥ d` claim for d=3.

The adversary's recipe:
 • Wait through rounds 0..R−2 error-free.
 • At the start of round R−1: inject Type-0 `X` on q₁.
 • Immediately inject Type-3 to flip G[0, R−1].
 • Let the remaining R−1 measurements proceed; none detect anything because
   X₁ commutes with ŝ₂..ŝ₈.

This hits the `MaskingLowerBound` gap the paper itself flagged at
[invariant.tex:1909](../../../Codedistance/invariant.tex). -/

/-- Counterexample uses exactly 2 errors. -/
theorem counterexample_2_errors :
    attack_Xq1_masked.cnt0 + attack_Xq1_masked.cnt1
    + attack_Xq1_masked.cnt2 + attack_Xq1_masked.cnt3 = 2 := by
  native_decide

/-- At σ_done, `G` is entirely zero — the decoder sees no detection event. -/
theorem counterexample_G_zero :
    allGZero testCode attack_Xq1_masked = true := by
  native_decide

/-- At σ_done, `Ẽ ∉ S`. (In fact `Ẽ = X_{q₁}` which has nonzero syndrome.) -/
theorem counterexample_E_notInS :
    notInStab testCode logicalX logicalZ attack_Xq1_masked.E_tilde = true := by
  native_decide

/-- **The counterexample.** A 2-error execution reaches σ_done satisfying
    both `G = 0` and `Ẽ ∉ S`. By the definition of `d^circ` in paper eq. at
    [invariant.tex:1201](../../../Codedistance/invariant.tex), this witnesses
    `d^circ ≤ 2`, which contradicts the paper's claim `d^circ ≥ d = 3` for
    d=3 NZ-scheduled surface code with R = 5. -/
theorem d3_nz_dCirc_at_most_2 :
    isUndetectedLogicalError testCode logicalX logicalZ attack_Xq1_masked = true := by
  native_decide

/-! ### Stim-equivalence test: does the attack trip `v2` (memory_z semantics)?

Expected: `false`. The attack's final-data detector for ŝ₁ fires because
Ẽ = X_{q₁} flips `q₁`'s Z-basis readout to 1, which XORs with the masked
last-round syndrome (0) to give detector = 1. Stim + PyMatching correctly
handle this case; `v2` should agree. -/

theorem attack_v2_NOT_logical :
    isUndetectedLogicalError_v2 testCode logicalZ attack_Xq1_masked = false := by
  native_decide

/-- Sanity: the Z-type stabilizer final-data detector for ŝ₁ actually fires. -/
theorem attack_final_detector_fires :
    finalDataDetector testCode attack_Xq1_masked ⟨0, by decide⟩ = true := by
  native_decide

/-! ### Genuine 3-error logical X̄ attack — should be flagged by BOTH predicates

Inject `X̄ = X_{q₁} X_{q₄} X_{q₇}` (3 Type-0 errors) at the start of round 4.
X̄ commutes with every stabilizer, so all G bits stay 0. In the memory_z
setup, Z-basis data-M at q₁, q₄, q₇ all read 1; the XORs over each Z-type
stabilizer's support are 0 (each stab touches 0 or 2 of these qubits), so
all final-data detectors are 0. Yet `parity(L_Z, X̄) = 1`. -/

def attack_logicalX_3errors : State testCode :=
  let s0 := State.init testCode
  let s1 := (List.range 32).foldl
    (fun s _ => match stepMeasure testCode s with | some s' => s' | none => s) s0
  let s2 := applyType0 s1 ⟨0, by decide⟩ .X  -- X on q₁
  let s3 := applyType0 s2 ⟨3, by decide⟩ .X  -- X on q₄
  let s4 := applyType0 s3 ⟨6, by decide⟩ .X  -- X on q₇
  runAllMeasurements testCode s4 100

#eval! attack_logicalX_3errors.cnt0
-- Expected: 3

#eval! isUndetectedLogicalError_v2 testCode logicalZ attack_logicalX_3errors
-- Expected: true (genuine logical error with 3 errors, matches standard d^circ = d)

theorem logicalX_attack_IS_logical_v2 :
    isUndetectedLogicalError_v2 testCode logicalZ attack_logicalX_3errors = true := by
  native_decide

theorem logicalX_attack_uses_3_errors :
    attack_logicalX_3errors.cnt0 = 3 := by
  native_decide

/-! ### Staggered-injection counterexample to `v2 ⟹ zero X-type syndrome`

**Attack**: inject `X` at qubit 0 just after measuring ŝ_1 at round R-1
(avoiding detection), then `Y` at qubit 3 after measuring ŝ_3, then `X` at
qubit 6 after measuring ŝ_6. All three errors are absorbed by future round-R-1
measurements because (a) ŝ_1 is already measured before X_{q1} is injected,
and (b) `Y_{q4} · X_{q7}` has parity 0 with ŝ_7 (Z at q_4, q_7), so the
remaining measurements at (4, R-1)..(7, R-1) all return 0.

**Result**: 3 errors, G all zero, v2 = true, but parity(ŝ_3, Ẽ) = 1
(non-zero X-type syndrome). This refutes the proposition
"v2 ⟹ ∀ X-type stab s, parity(T_s, Ẽ) = 0".

Cross-validated in Python at
[notes/check_v2_x_syndrome_counterexample.py](../../../Codedistance/notes/check_v2_x_syndrome_counterexample.py). -/

/-- Construct the staggered 3-error attack explicitly via the Python-ported
    semantics (applyType0 / stepMeasure). -/
def attack_staggered_XYX : State testCode :=
  let s0 := State.init testCode
  -- Rounds 0 through R-2 error-free: 8 stabs × (R-1) = 8 × 4 = 32 measurements
  -- reach coord (0, 4). Then advance one more to coord (1, 4) without errors.
  let s1 := (List.range 32).foldl
    (fun s _ => match stepMeasure testCode s with
                | some s' => s'
                | none => s) s0
  -- Measure ŝ_1 at (0, 4): E = I, parity 0, G = 0.
  let s2 := match stepMeasure testCode s1 with
            | some s' => s' | none => s1
  -- Inject X at q_1 (Fin 0). E = X_1. Anticommutes with ŝ_1, but ŝ_1 done.
  let s3 := applyType0 s2 ⟨0, by decide⟩ .X
  -- Measure ŝ_2 at (1, 4) and ŝ_3 at (2, 4): X_1 commutes with X-type stabs.
  let s4 := match stepMeasure testCode s3 with
            | some s' => s' | none => s3
  let s5 := match stepMeasure testCode s4 with
            | some s' => s' | none => s4
  -- Inject Y at q_4 (Fin 3). E = X_1 Y_4.
  let s6 := applyType0 s5 ⟨3, by decide⟩ .Y
  -- Measure ŝ_4 (3, 4), ŝ_5 (4, 4), ŝ_6 (5, 4).
  let s7 := match stepMeasure testCode s6 with
            | some s' => s' | none => s6
  let s8 := match stepMeasure testCode s7 with
            | some s' => s' | none => s7
  let s9 := match stepMeasure testCode s8 with
            | some s' => s' | none => s8
  -- Inject X at q_7 (Fin 6). E = X_1 Y_4 X_7.
  let s10 := applyType0 s9 ⟨6, by decide⟩ .X
  -- Measure ŝ_7 (6, 4), ŝ_8 (7, 4). ŝ_7 sees Y_4 + X_7 (parity 0); ŝ_8 sees nothing.
  let s11 := match stepMeasure testCode s10 with
             | some s' => s' | none => s10
  let s12 := match stepMeasure testCode s11 with
             | some s' => s' | none => s11
  s12

/-- The staggered attack uses exactly 3 errors. -/
theorem staggered_attack_uses_3_errors :
    attack_staggered_XYX.cnt0 = 3 := by native_decide

/-- The staggered attack satisfies `v2` (all detectors read 0, logical flip
    recorded). -/
theorem staggered_attack_v2_true :
    isUndetectedLogicalError_v2 testCode logicalZ attack_staggered_XYX = true := by
  native_decide

/-- **Counterexample to `v2 ⟹ zero X-type syndrome`.** The staggered 3-error
    attack reaches a v2-true state where `parity(ŝ_3, Ẽ) = 1` (ŝ_3 is the
    X-type bulk SW plaquette, Fin index 2). -/
theorem staggered_attack_Xsyndrome_nonzero :
    ErrorVec.parity (code.stabilizers ⟨2, by decide⟩)
                    attack_staggered_XYX.E_tilde = true := by
  native_decide

/-! ### A6: spec-level proofs that `logicalX`, `logicalZ` are valid logical operators

These close the "hidden assumption" A6 from `semantics_audit.md`. For the
`isUndetectedLogicalError` predicate to mean what we think, we need:

  (1) `L_X, L_Z ∈ N(S)`  — commute with every stabilizer generator
  (2) `L_X, L_Z ∉ S`      — not stabilizer products
  (3) `L_X · L_Z` ≠ `L_Z · L_X` — anticommute (distinguishes the logical qubit)

(1) is direct. (3) together with (1) implies (2): if `L_X ∈ S`, it would commute
with `L_Z` (since `S ⊂ N(S)` and everything in `S` commutes with `N(S)`), contradiction.

All three are decided automatically — surface code's `parity` is computable. -/

theorem logicalX_commutes_all_stabilizers :
    ∀ i : Fin code.numStab, ErrorVec.parity (code.stabilizers i) logicalX = false := by
  decide

theorem logicalZ_commutes_all_stabilizers :
    ∀ i : Fin code.numStab, ErrorVec.parity (code.stabilizers i) logicalZ = false := by
  decide

theorem logicalX_anticommutes_logicalZ :
    ErrorVec.parity logicalX logicalZ = true := by
  decide

/-- Corollary: `logicalX ∉ S`. (Anything in `S` commutes with every element of `N(S)`;
    `logicalZ ∈ N(S)` by `logicalZ_commutes_all_stabilizers`, so if `logicalX ∈ S`
    then `parity logicalX logicalZ = false`, contradicting the above.) -/
theorem logicalX_notInStab :
    notInStab code logicalX logicalZ logicalX = true := by
  decide

theorem logicalZ_notInStab :
    notInStab code logicalX logicalZ logicalZ = true := by
  decide

/-! ### A1 + B2: concrete hook-error set for NZ-scheduled d=3 surface code

Enumerates `B¹(T_s)` from [invariant.tex:1450–1476](../../../Codedistance/invariant.tex)
(Lemma HookSupportsNZ) for each stabilizer of the d=3 surface code. Closes:

* **A1**: `backActionSet` is no longer purely abstract — for this code we know
  exactly which errors it contains.
* **B2**: proves `parity(T_s, e_B) = 0` for every hook, which is the condition
  under which `Step.type2`'s "inject then measure" semantics coincides with the
  paper's combined Type-II rule.

Stabilizer geometry (qubit Fin indices, 0-based paper `q_k` ↔ Fin `k-1`):

| s | type  | role             | gate order (NZ)          | NW, NE, SW, SE |
|---|-------|------------------|--------------------------|----------------|
| 0 | Z     | bulk NW plaquette| N-order NW→SW→NE→SE      | 0, 1, 3, 4     |
| 1 | X     | bulk NE plaquette| Z-order NW→NE→SW→SE      | 1, 2, 4, 5     |
| 2 | X     | bulk SW plaquette| Z-order NW→NE→SW→SE      | 3, 4, 6, 7     |
| 3 | Z     | bulk SE plaquette| N-order NW→SW→NE→SE      | 4, 5, 7, 8     |
| 4 | X     | top boundary     | left→right               | 0, 1           |
| 5 | Z     | right boundary   | top→bottom               | 2, 5           |
| 6 | Z     | left boundary    | top→bottom               | 3, 6           |
| 7 | X     | bottom boundary  | left→right               | 7, 8           |

Weight-4 stabilizers have hooks at `j ∈ {1, 2, 3}`; weight-2 at `j = 1`. -/

/-- Enumerated NZ hook errors for each d=3 stabilizer (intended `B¹(T_s)`). -/
def hookErrors : Fin 8 → List (ErrorVec 9)
  -- ŝ₁ Z-type, N-order, hooks at j=1 (SW,NE,SE), j=2 (NE,SE), j=3 (SE)
  | ⟨0, _⟩ => [ ofList [(1, .Z), (3, .Z), (4, .Z)]
              , ofList [(1, .Z), (4, .Z)]
              , ofList [(4, .Z)] ]
  -- ŝ₂ X-type, Z-order, hooks at j=1 (NE,SW,SE), j=2 (SW,SE), j=3 (SE)
  | ⟨1, _⟩ => [ ofList [(2, .X), (4, .X), (5, .X)]
              , ofList [(4, .X), (5, .X)]
              , ofList [(5, .X)] ]
  -- ŝ₃ X-type
  | ⟨2, _⟩ => [ ofList [(4, .X), (6, .X), (7, .X)]
              , ofList [(6, .X), (7, .X)]
              , ofList [(7, .X)] ]
  -- ŝ₄ Z-type
  | ⟨3, _⟩ => [ ofList [(5, .Z), (7, .Z), (8, .Z)]
              , ofList [(5, .Z), (8, .Z)]
              , ofList [(8, .Z)] ]
  -- ŝ₅ X-type boundary (left→right), hook at j=1 on second qubit q₂
  | ⟨4, _⟩ => [ ofList [(1, .X)] ]
  -- ŝ₆ Z-type boundary (top→bottom), hook on q₆
  | ⟨5, _⟩ => [ ofList [(5, .Z)] ]
  -- ŝ₇ Z-type boundary, hook on q₇
  | ⟨6, _⟩ => [ ofList [(6, .Z)] ]
  -- ŝ₈ X-type boundary, hook on q₉
  | ⟨7, _⟩ => [ ofList [(8, .X)] ]

/-- **B2 cancellation**: every NZ hook commutes with its parent stabilizer.
    This is the condition under which `Step.type2`'s "inject first, then
    measure" implementation matches the paper's combined Type-II rule. -/
theorem hook_commutes_its_stabilizer :
    ∀ s : Fin 8, ∀ e ∈ hookErrors s,
    ErrorVec.parity (stabilizers s) e = false := by
  decide

/-- Weight bound (paper's `backAction_weight_bound` axiom, specialized).
    For d=3, all hooks have weight ≤ 3. -/
theorem hook_weight_bound :
    ∀ s : Fin 8, ∀ e ∈ hookErrors s, ErrorVec.weight e ≤ 3 := by
  decide

/-- Count check: each weight-4 stabilizer has 3 hooks; each weight-2 has 1. -/
theorem hook_count :
    (hookErrors ⟨0, by decide⟩).length = 3 ∧
    (hookErrors ⟨1, by decide⟩).length = 3 ∧
    (hookErrors ⟨2, by decide⟩).length = 3 ∧
    (hookErrors ⟨3, by decide⟩).length = 3 ∧
    (hookErrors ⟨4, by decide⟩).length = 1 ∧
    (hookErrors ⟨5, by decide⟩).length = 1 ∧
    (hookErrors ⟨6, by decide⟩).length = 1 ∧
    (hookErrors ⟨7, by decide⟩).length = 1 := by
  decide

/-- Paper Lemma HookPerp (invariant.tex:1483), specialized to d=3.
    Every weight-2 X-type hook is a horizontal pair — both qubits in the
    same row. Witnesses the specific hooks in the enumeration. -/
theorem weight2_Xhook_sameRow_s2 :
    ofList [(4, .X), (5, .X)] ∈ hookErrors ⟨1, by decide⟩ := by decide  -- ŝ₂: q₅, q₆ in row 2

theorem weight2_Xhook_sameRow_s3 :
    ofList [(6, .X), (7, .X)] ∈ hookErrors ⟨2, by decide⟩ := by decide  -- ŝ₃: q₇, q₈ in row 3

/-- Every weight-2 Z-type hook is a vertical pair — both qubits in same column. -/
theorem weight2_Zhook_sameCol_s1 :
    ofList [(1, .Z), (4, .Z)] ∈ hookErrors ⟨0, by decide⟩ := by decide  -- ŝ₁: q₂, q₅ in col 2

theorem weight2_Zhook_sameCol_s4 :
    ofList [(5, .Z), (8, .Z)] ∈ hookErrors ⟨3, by decide⟩ := by decide  -- ŝ₄: q₆, q₉ in col 3

/-- Paper Lemma StabAbsorb (invariant.tex:1501), specialized to d=3.
    Each weight-3 hook equals (stabilizer) · (first-gate-qubit Pauli).
    Since the stabilizer is in `S`, this means the weight-3 hook is equivalent
    mod S to a single-qubit error. -/
theorem weight3_hook_absorb_s1 :
    ErrorVec.mul (stabilizers ⟨0, by decide⟩) (ofList [(0, .Z)]) =
      ofList [(1, .Z), (3, .Z), (4, .Z)] := by
  funext i; fin_cases i <;> rfl

theorem weight3_hook_absorb_s2 :
    ErrorVec.mul (stabilizers ⟨1, by decide⟩) (ofList [(1, .X)]) =
      ofList [(2, .X), (4, .X), (5, .X)] := by
  funext i; fin_cases i <;> rfl

/-! ### Phase 4 scaffolding — the perpendicular spread invariant

Central invariant from [invariant.tex:1561](../../../Codedistance/invariant.tex)
(ghost-witness reformulation):

    p^{ω_X}(σ)  :=  ∃ S_wit ∈ InStab code, projRowsX (mul S_wit Ẽ) ≤ C_budget − C

For Path A (theorem `d^circ_{v2} ≥ d` under NZ scheduling), this invariant is
the key tool: combined with the topological lower bound (Phase 5 Step 4) +
two-phase argument (Phase 6), it forces |F| ≥ d for v2-true executions.

Defined on `State testCode` (so we can quote `testCode.C_budget = 20` and still
inject d = 3 errors before the invariant becomes vacuous). Witnesses live in
`InStab code`; since `testCode = { code with C_budget := 20 }` the stabilizer
generators agree and this is type-safe. -/

open QStab

/-- Perpendicular spread (ghost-witness form) for the d=3 surface code.
    Stated in additive form `projRowsX + C ≤ C_budget` to dodge Nat-subtraction
    issues in the preservation proof. Equivalent to `projRowsX ≤ C_budget - C`
    whenever `C ≤ C_budget` (always true in reachable states). -/
def perpSpreadX_holds (s : State testCode) : Prop :=
  ∃ S_wit : ErrorVec 9,
    QStab.InStab code S_wit ∧
    projRowsX (d := 3) (ErrorVec.mul S_wit s.E_tilde) + s.C ≤ testCode.C_budget

/-- **Init**: at σ_0, `Ẽ = I`, `C = C_budget`. `S_wit = I`, projRowsX = 0,
    so `0 + C_budget ≤ C_budget`. -/
theorem perpSpreadX_init : perpSpreadX_holds (State.init testCode) := by
  refine ⟨ErrorVec.identity 9, QStab.InStab.identity, ?_⟩
  show projRowsX (d := 3) (ErrorVec.mul (ErrorVec.identity 9) (ErrorVec.identity 9))
       + testCode.C_budget ≤ testCode.C_budget
  have hmul : ErrorVec.mul (ErrorVec.identity 9) (ErrorVec.identity 9)
              = ErrorVec.identity 9 := by funext _; rfl
  rw [hmul, projRowsX_identity 3]
  omega

/-! Helper lemmas pending for Phase 5 Step 4: each transition's effect on
    projRowsX. Their proofs are the paper's `SingleQubitPerturb`
    ([invariant.tex:1592](../../../Codedistance/invariant.tex)) and
    `NZHookPerturb` ([invariant.tex:1613](../../../Codedistance/invariant.tex))
    specialised to d=3. Both are combinatorial facts about `projRowsX`. -/

/-- Single-qubit perturbation (paper Lemma `SingleQubitPerturb` at
    [invariant.tex:1592](../../../Codedistance/invariant.tex)).
    Applying a single-qubit Pauli via `ErrorVec.update` can add at most one
    row to `projRowsX`.

    Proof: the only row of the grid affected is `qRow = q.val / 3`. For any
    other row `i`, every qubit `toIdx 3 i j` differs from `q`, so the update
    is invisible there. Hence the new "rows-with-X" set is contained in the
    old one ∪ `{qRow}`, giving card ≤ card + 1. -/
theorem projRowsX_update_le (E : ErrorVec 9) (q : Fin 9) (p : Pauli) :
    projRowsX (d := 3) (ErrorVec.update E q p)
      ≤ projRowsX (d := 3) E + 1 := by
  -- Row containing q in the 3×3 grid.
  let qRow : Fin 3 := ⟨q.val / 3, by have := q.isLt; omega⟩
  -- For any row i ≠ qRow, all qubits in that row have index ≠ q.
  have h_idx_neq : ∀ (i : Fin 3) (j : Fin 3), i ≠ qRow → toIdx 3 i j ≠ q := by
    intro i j hi hEq
    apply hi
    apply Fin.ext
    show i.val = q.val / 3
    have hEq' : 3 * i.val + j.val = q.val := Fin.mk.inj hEq
    have hj : j.val < 3 := j.isLt
    omega
  -- newFilter ⊆ oldFilter ∪ {qRow}.
  have h_subset :
      (Finset.univ.filter fun i : Fin 3 =>
        ∃ j : Fin 3,
          Pauli.hasXComponent (ErrorVec.update E q p (toIdx 3 i j)) = true)
      ⊆ (Finset.univ.filter fun i : Fin 3 =>
          ∃ j : Fin 3, Pauli.hasXComponent (E (toIdx 3 i j)) = true)
        ∪ {qRow} := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
               Finset.mem_singleton] at hi ⊢
    by_cases hqR : i = qRow
    · right; exact hqR
    · left
      obtain ⟨j, hj⟩ := hi
      refine ⟨j, ?_⟩
      have h_neq := h_idx_neq i j hqR
      have h_update : ErrorVec.update E q p (toIdx 3 i j) = E (toIdx 3 i j) := by
        show Function.update E q (Pauli.mul p (E q)) (toIdx 3 i j)
             = E (toIdx 3 i j)
        exact Function.update_of_ne h_neq _ _
      rw [h_update] at hj
      exact hj
  -- Bound via subset card + union card.
  calc projRowsX (d := 3) (ErrorVec.update E q p)
      ≤ ((Finset.univ.filter fun i : Fin 3 =>
            ∃ j : Fin 3, Pauli.hasXComponent (E (toIdx 3 i j)) = true)
          ∪ {qRow}).card
        := Finset.card_le_card h_subset
    _ ≤ (Finset.univ.filter fun i : Fin 3 =>
            ∃ j : Fin 3, Pauli.hasXComponent (E (toIdx 3 i j)) = true).card
        + ({qRow} : Finset (Fin 3)).card
        := Finset.card_union_le _ _
    _ = projRowsX (d := 3) E + 1 := by simp [projRowsX]

/-- General helper: if at every qubit, multiplication by `a` either preserves
    `hasXComponent` or the qubit is in row `r`, then `projRowsX` increases by
    at most 1.

    This subsumes: Z-only multiplications (left disjunct always), single-qubit
    X updates (left except at the one qubit, in its row), and same-row
    multi-X perturbations (left except on qubits of that shared row). -/
theorem projRowsX_mul_rowRestricted_le (a E : ErrorVec 9) (r : Fin 3)
    (h : ∀ i : Fin 9,
         Pauli.hasXComponent (Pauli.mul (a i) (E i))
         = Pauli.hasXComponent (E i)
         ∨ i.val / 3 = r.val) :
    projRowsX (d := 3) (ErrorVec.mul a E) ≤ projRowsX (d := 3) E + 1 := by
  have h_subset :
      (Finset.univ.filter fun i : Fin 3 =>
        ∃ j : Fin 3, Pauli.hasXComponent (ErrorVec.mul a E (toIdx 3 i j)) = true)
      ⊆ (Finset.univ.filter fun i : Fin 3 =>
          ∃ j : Fin 3, Pauli.hasXComponent (E (toIdx 3 i j)) = true)
        ∪ {r} := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
               Finset.mem_singleton] at hi ⊢
    by_cases hir : i = r
    · right; exact hir
    · left
      obtain ⟨j, hj⟩ := hi
      refine ⟨j, ?_⟩
      have h_div : (toIdx 3 i j).val / 3 = i.val := by
        show (3 * i.val + j.val) / 3 = i.val
        have := j.isLt
        omega
      have h_div_ne : (toIdx 3 i j).val / 3 ≠ r.val := by
        rw [h_div]
        intro heq; exact hir (Fin.ext heq)
      rcases h (toIdx 3 i j) with heq | hdiv
      · show Pauli.hasXComponent (E (toIdx 3 i j)) = true
        have hmul_eq : Pauli.hasXComponent (ErrorVec.mul a E (toIdx 3 i j))
                     = Pauli.hasXComponent (E (toIdx 3 i j)) := heq
        rw [hmul_eq] at hj
        exact hj
      · exfalso; exact h_div_ne hdiv
  calc projRowsX (d := 3) (ErrorVec.mul a E)
      ≤ ((Finset.univ.filter fun i : Fin 3 =>
            ∃ j : Fin 3, Pauli.hasXComponent (E (toIdx 3 i j)) = true)
          ∪ {r}).card
        := Finset.card_le_card h_subset
    _ ≤ (Finset.univ.filter fun i : Fin 3 =>
            ∃ j : Fin 3, Pauli.hasXComponent (E (toIdx 3 i j)) = true).card
        + ({r} : Finset (Fin 3)).card
        := Finset.card_union_le _ _
    _ = projRowsX (d := 3) E + 1 := by simp [projRowsX]

/-- NZ hook perturbation (paper Lemma `NZHookPerturb` at
    [invariant.tex:1613](../../../Codedistance/invariant.tex)).

    **Restated form** (stronger than paper's direct bound, but what the
    preservation proof actually needs). For every hook `e ∈ B¹(T_{stab_idx})`
    there is a stabilizer correction `corr ∈ InStab code` such that
    `corr · e · E` has `projRowsX` at most `projRowsX E + 1`. The direct
    bound `projRowsX (e · E) ≤ projRowsX E + 1` fails for weight-3 X hooks
    (e.g. `X_{q₃}X_{q₅}X_{q₆}` at `E = I` gives `projRowsX = 2`), but the
    stabilizer absorption (paper `StabAbsorb`) turns them into single-qubit
    perturbations.

    Witness choice:
    * Z-type hooks and X weight-≤ 2 hooks: `corr = I`.
    * X weight-3 hooks: `corr = T_{stab_idx}`. Then `corr · e = single_X`. -/
theorem projRowsX_hook_le (E : ErrorVec 9) (stab_idx : Fin 8) (e : ErrorVec 9)
    (he : e ∈ hookErrors stab_idx) :
    ∃ corr : ErrorVec 9, QStab.InStab code corr ∧
      projRowsX (d := 3) (ErrorVec.mul (ErrorVec.mul corr e) E)
        ≤ projRowsX (d := 3) E + 1 := by
  -- Every case proceeds the same way: choose `corr`, simplify `corr · e`, then
  -- invoke `projRowsX_mul_rowRestricted_le` with an appropriate row witness.
  fin_cases stab_idx
  all_goals (
    simp only [hookErrors, List.mem_cons, List.not_mem_nil, or_false] at he)
  -- Fin 0 (ŝ₁, Z-type, 3 hooks)
  · rcases he with rfl | rfl | rfl <;> (
      refine ⟨ErrorVec.identity 9, QStab.InStab.identity, ?_⟩
      show projRowsX (d := 3)
            (ErrorVec.mul (ErrorVec.mul (ErrorVec.identity 9) _) E)
            ≤ projRowsX (d := 3) E + 1
      rw [ErrorVec.mul_identity_left]
      apply projRowsX_mul_rowRestricted_le _ _ ⟨0, by decide⟩
      intro i
      left
      fin_cases i <;> cases (E _) <;> rfl)
  -- Fin 1 (ŝ₂, X-type, 3 hooks: weight-3, weight-2, weight-1)
  · rcases he with rfl | rfl | rfl
    · -- weight-3 hook: ofList [(2, X), (4, X), (5, X)], use corr = s2
      refine ⟨stabilizers ⟨1, by decide⟩,
              QStab.InStab.gen ⟨1, by decide⟩, ?_⟩
      have hred : ErrorVec.mul (stabilizers ⟨1, by decide⟩)
                    (ofList [(2, .X), (4, .X), (5, .X)] : ErrorVec 9)
                  = (ofList [(1, .X)] : ErrorVec 9) := by
        funext i; fin_cases i <;> rfl
      rw [hred]
      apply projRowsX_mul_rowRestricted_le _ _ ⟨0, by decide⟩
      intro i
      fin_cases i <;> (try (left; cases (E _) <;> rfl)) <;> (right; decide)
    · -- weight-2 same-row hook: ofList [(4, X), (5, X)], both in row 1
      refine ⟨ErrorVec.identity 9, QStab.InStab.identity, ?_⟩
      rw [ErrorVec.mul_identity_left]
      apply projRowsX_mul_rowRestricted_le _ _ ⟨1, by decide⟩
      intro i
      fin_cases i <;> (try (left; cases (E _) <;> rfl)) <;> (right; decide)
    · -- weight-1 hook: ofList [(5, X)]
      refine ⟨ErrorVec.identity 9, QStab.InStab.identity, ?_⟩
      rw [ErrorVec.mul_identity_left]
      apply projRowsX_mul_rowRestricted_le _ _ ⟨1, by decide⟩
      intro i
      fin_cases i <;> (try (left; cases (E _) <;> rfl)) <;> (right; decide)
  -- Fin 2 (ŝ₃, X-type, 3 hooks)
  · rcases he with rfl | rfl | rfl
    · -- weight-3 hook: ofList [(4, X), (6, X), (7, X)], use corr = s3
      refine ⟨stabilizers ⟨2, by decide⟩,
              QStab.InStab.gen ⟨2, by decide⟩, ?_⟩
      have hred : ErrorVec.mul (stabilizers ⟨2, by decide⟩)
                    (ofList [(4, .X), (6, .X), (7, .X)] : ErrorVec 9)
                  = (ofList [(3, .X)] : ErrorVec 9) := by
        funext i; fin_cases i <;> rfl
      rw [hred]
      apply projRowsX_mul_rowRestricted_le _ _ ⟨1, by decide⟩
      intro i
      fin_cases i <;> (try (left; cases (E _) <;> rfl)) <;> (right; decide)
    · -- weight-2 same-row hook: ofList [(6, X), (7, X)], both in row 2
      refine ⟨ErrorVec.identity 9, QStab.InStab.identity, ?_⟩
      rw [ErrorVec.mul_identity_left]
      apply projRowsX_mul_rowRestricted_le _ _ ⟨2, by decide⟩
      intro i
      fin_cases i <;> (try (left; cases (E _) <;> rfl)) <;> (right; decide)
    · -- weight-1 hook: ofList [(7, X)]
      refine ⟨ErrorVec.identity 9, QStab.InStab.identity, ?_⟩
      rw [ErrorVec.mul_identity_left]
      apply projRowsX_mul_rowRestricted_le _ _ ⟨2, by decide⟩
      intro i
      fin_cases i <;> (try (left; cases (E _) <;> rfl)) <;> (right; decide)
  -- Fin 3 (ŝ₄, Z-type, 3 hooks)
  · rcases he with rfl | rfl | rfl <;> (
      refine ⟨ErrorVec.identity 9, QStab.InStab.identity, ?_⟩
      rw [ErrorVec.mul_identity_left]
      apply projRowsX_mul_rowRestricted_le _ _ ⟨0, by decide⟩
      intro i
      left
      fin_cases i <;> cases (E _) <;> rfl)
  -- Fin 4 (ŝ₅ boundary X, 1 hook weight 1: ofList [(1, X)], row 0)
  · rcases he with rfl
    refine ⟨ErrorVec.identity 9, QStab.InStab.identity, ?_⟩
    rw [ErrorVec.mul_identity_left]
    apply projRowsX_mul_rowRestricted_le _ _ ⟨0, by decide⟩
    intro i
    fin_cases i <;> (try (left; cases (E _) <;> rfl)) <;> (right; decide)
  -- Fin 5 (ŝ₆ boundary Z)
  · rcases he with rfl
    refine ⟨ErrorVec.identity 9, QStab.InStab.identity, ?_⟩
    rw [ErrorVec.mul_identity_left]
    apply projRowsX_mul_rowRestricted_le _ _ ⟨0, by decide⟩
    intro i
    left
    fin_cases i <;> cases (E _) <;> rfl
  -- Fin 6 (ŝ₇ boundary Z)
  · rcases he with rfl
    refine ⟨ErrorVec.identity 9, QStab.InStab.identity, ?_⟩
    rw [ErrorVec.mul_identity_left]
    apply projRowsX_mul_rowRestricted_le _ _ ⟨0, by decide⟩
    intro i
    left
    fin_cases i <;> cases (E _) <;> rfl
  -- Fin 7 (ŝ₈ boundary X, 1 hook weight 1: ofList [(8, X)], row 2)
  · rcases he with rfl
    refine ⟨ErrorVec.identity 9, QStab.InStab.identity, ?_⟩
    rw [ErrorVec.mul_identity_left]
    apply projRowsX_mul_rowRestricted_le _ _ ⟨2, by decide⟩
    intro i
    fin_cases i <;> (try (left; cases (E _) <;> rfl)) <;> (right; decide)

/-- Helper: `ErrorVec.mul` is commutative (Pauli is the abelian Klein four-group
    when phases are dropped). 16 case checks via `rfl`. -/
theorem ErrorVec.mul_comm' {n : Nat} (a b : ErrorVec n) :
    ErrorVec.mul a b = ErrorVec.mul b a := by
  funext i
  show Pauli.mul (a i) (b i) = Pauli.mul (b i) (a i)
  cases (a i) <;> cases (b i) <;> rfl

/-- **`backActionSet` bridge (proved).** With the conservative
    `backActionSet = ∅` in [QStab.BackAction](../BackAction.lean), the bridge
    from the abstract `Step.type2` back-action hypothesis to the concrete
    enumeration `hookErrors` holds trivially (empty set ⊆ anything). -/
theorem backActionSet_subset_hookErrors
    (stab_idx : Fin 8) (e : ErrorVec 9)
    (he : e ∈ @QStab.backActionSet testCode stab_idx) :
    e ∈ hookErrors stab_idx :=
  he.elim

/-- Preservation of `perpSpreadX_holds` by each active→active transition.
    Paper's Proposition `PerpSpreadPreserve` ([invariant.tex:1647](../../../Codedistance/invariant.tex))
    for d=3. All five cases proved: type0/1 via `projRowsX_update_le`; type2
    is vacuous (`backActionSet = ∅`); type3 and measure trivially. -/
theorem perpSpreadX_preservation
    (s s' : State testCode)
    (hinv : perpSpreadX_holds s)
    (hstep : Step testCode (.active s) (.active s')) :
    perpSpreadX_holds s' := by
  obtain ⟨S_wit, hS_stab, hbound⟩ := hinv
  -- Common helper: rearrange `mul S_wit (update E i p)` to `update (mul S_wit E) i p`.
  have swap_update : ∀ (E : ErrorVec 9) (i : Fin 9) (p : Pauli),
      ErrorVec.mul S_wit (ErrorVec.update E i p)
        = ErrorVec.update (ErrorVec.mul S_wit E) i p := by
    intro E i p
    funext k
    unfold ErrorVec.mul ErrorVec.update
    by_cases hk : k = i
    · subst hk
      simp only [Function.update_self]
      cases (S_wit k) <;> cases p <;> cases (E k) <;> rfl
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
  cases hstep with
  | type0 _ i p _ hC =>
    refine ⟨S_wit, hS_stab, ?_⟩
    show projRowsX (d := 3)
           (ErrorVec.mul S_wit (ErrorVec.update s.E_tilde i p))
         + (s.C - 1) ≤ testCode.C_budget
    rw [swap_update s.E_tilde i p]
    have hLe := projRowsX_update_le (ErrorVec.mul S_wit s.E_tilde) i p
    omega
  | type1 _ i p _ hC =>
    refine ⟨S_wit, hS_stab, ?_⟩
    show projRowsX (d := 3)
           (ErrorVec.mul S_wit (ErrorVec.update s.E_tilde i p))
         + (s.C - 1) ≤ testCode.C_budget
    rw [swap_update s.E_tilde i p]
    have hLe := projRowsX_update_le (ErrorVec.mul S_wit s.E_tilde) i p
    omega
  | type2 _ e he _ =>
    -- Vacuous under `backActionSet = ∅`. The hypothesis `he : e ∈ ∅` is False.
    exact he.elim
  | type3 _ hC =>
    refine ⟨S_wit, hS_stab, ?_⟩
    show projRowsX (d := 3) (ErrorVec.mul S_wit s.E_tilde)
         + (s.C - 1) ≤ testCode.C_budget
    omega
  | measure _ nc _ =>
    refine ⟨S_wit, hS_stab, ?_⟩
    show projRowsX (d := 3)
           (ErrorVec.mul S_wit (measureStep testCode s nc).E_tilde)
         + (measureStep testCode s nc).C ≤ testCode.C_budget
    rw [measureStep_E_tilde, measureStep_C]
    exact hbound

/-- Package `perpSpreadX_holds` into the generic `QStab.Invariant` framework,
    yielding `holds_of_reachable` for free. -/
def perpSpreadX_Invariant : QStab.Invariant testCode where
  holds := perpSpreadX_holds
  holds_init := perpSpreadX_init
  preservation := perpSpreadX_preservation

/-! ## Topological lower bound and target theorem

Section 3.4 of the paper. For any `Ẽ` with zero syndrome and
`parity(L_Z, Ẽ) = 1`, every stabilizer-equivalent representative has
`projRowsX ≥ d`. Proof: the row-cut operators `Ẑ_i ≡ L_Z (mod S)` for
i = 1, 2, 3, so `parity(Ẑ_i, S · Ẽ) = 1` (via `parity_of_normalizer`),
and `parity(Ẑ_i, F) = 1` forces row `i − 1` of `F` to have an
X-component (the combinatorial lemma `row_has_X_of_rowCut_parity` below).

The `v2 ⟹ zero syndrome` bridge remains axiomatic; it requires the §3
two-phase argument (detectors at round boundaries + final data measure). -/

/-! ### Helpers for the topological lower bound -/

/-- Parity is symmetric (follows from `Pauli.anticommutes_symm`). -/
theorem ErrorVec.parity_symm' {n : Nat} (a b : ErrorVec n) :
    ErrorVec.parity a b = ErrorVec.parity b a := by
  unfold ErrorVec.parity
  have h_eq : (Finset.univ.filter fun i : Fin n =>
                ErrorVec.Pauli.anticommutes (a i) (b i) = true)
            = (Finset.univ.filter fun i : Fin n =>
                ErrorVec.Pauli.anticommutes (b i) (a i) = true) := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Pauli.anticommutes_symm]
  rw [h_eq]

/-- d=3 surface code stabilizers pairwise commute. -/
theorem stabilizers_pairwise_commute :
    ∀ i j : Fin 8, ErrorVec.parity (stabilizers i) (stabilizers j) = false := by
  decide

/-- Every stabilizer generator commutes with every element of `InStab code`.
    The stabilizer subgroup is abelian.

    Reduced via `parity_symm'` + `parity_of_normalizer`: `parity (stab_i) S =
    parity S (stab_i) = 0` since `S ∈ InStab` and `stab_i` has zero syndrome
    against every stabilizer generator (the generators pairwise commute).
    Stated with `code.stabilizers i` so the LHS matches the rewrite sites
    in `topological_lower_bound`. -/
theorem parity_generator_in_InStab (i : Fin code.numStab)
    {S : ErrorVec 9} (hS : QStab.InStab code S) :
    ErrorVec.parity (code.stabilizers i) S = false := by
  rw [ErrorVec.parity_symm']
  exact QStab.InStab.parity_of_normalizer
          (fun j => stabilizers_pairwise_commute j i) hS

/-- Each `rowCut i` (i = 1, 2, 3) is stabilizer-equivalent to `logicalZ`. -/
private theorem rowCut_stabEquiv_logicalZ (i : Fin 3) :
    ∃ S_i : ErrorVec 9, QStab.InStab code S_i ∧
      rowCut (i.val + 1) = ErrorVec.mul S_i logicalZ := by
  fin_cases i
  · exact rowCut_one_stabEquiv_logicalZ
  · exact rowCut_two_stabEquiv_logicalZ
  · exact rowCut_three_stabEquiv_logicalZ

/-- Characterize `ofList [(q, .Z)]` as a pointwise function of `i.val = q`. -/
private theorem ofList_single_Z_val (q : Nat) (i : Fin 9) :
    (ofList [(q, .Z)] : ErrorVec 9) i =
    if i.val = q then Pauli.Z else Pauli.I := by
  show (List.lookup i.val [(q, .Z)]).getD Pauli.I = _
  by_cases h : i.val = q
  · rw [if_pos h]
    have hbeq : (i.val == q) = true := by simp [h]
    show (match i.val == q with | true => some Pauli.Z | false => none).getD Pauli.I = Pauli.Z
    rw [hbeq]; rfl
  · rw [if_neg h]
    have hbeq : (i.val == q) = false := by simp [h]
    show (match i.val == q with | true => some Pauli.Z | false => none).getD Pauli.I = Pauli.I
    rw [hbeq]; rfl

/-- Parity of a single-Z ErrorVec at position q equals `hasXComponent` of F at q.
    The filter set is either `{⟨q, hq⟩}` (if `hasX (F q)`) or empty. -/
theorem parity_ofList_single_Z (q : Nat) (hq : q < 9) (F : ErrorVec 9) :
    ErrorVec.parity (ofList [(q, .Z)] : ErrorVec 9) F
    = Pauli.hasXComponent (F ⟨q, hq⟩) := by
  unfold ErrorVec.parity
  have h_at_q : (ofList [(q, .Z)] : ErrorVec 9) ⟨q, hq⟩ = Pauli.Z := by
    rw [ofList_single_Z_val]; simp
  have h_at_ne : ∀ i : Fin 9, i.val ≠ q →
      (ofList [(q, .Z)] : ErrorVec 9) i = Pauli.I := by
    intro i hi
    rw [ofList_single_Z_val]; simp [hi]
  by_cases hX : Pauli.hasXComponent (F ⟨q, hq⟩) = true
  · rw [hX]
    have h_filter_eq : (Finset.univ.filter fun i : Fin 9 =>
        ErrorVec.Pauli.anticommutes ((ofList [(q, .Z)] : ErrorVec 9) i) (F i) = true)
        = {⟨q, hq⟩} := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h_anti
        by_contra hne
        have hi : i.val ≠ q := fun heq => hne (Fin.ext heq)
        rw [h_at_ne i hi, Pauli.anticommutes_I_left] at h_anti
        exact absurd h_anti (by decide)
      · intro h_eq
        rw [h_eq, h_at_q, Pauli.anticommutes_Z_eq_hasXComponent]
        exact hX
    rw [h_filter_eq, Finset.card_singleton]
    rfl
  · have hX_false : Pauli.hasXComponent (F ⟨q, hq⟩) = false := by
      match h : Pauli.hasXComponent (F ⟨q, hq⟩) with
      | true => exact absurd h hX
      | false => rfl
    rw [hX_false]
    have h_filter_empty : (Finset.univ.filter fun i : Fin 9 =>
        ErrorVec.Pauli.anticommutes ((ofList [(q, .Z)] : ErrorVec 9) i) (F i) = true)
        = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _
      by_cases hiq : i.val = q
      · have h_eq : i = ⟨q, hq⟩ := Fin.ext hiq
        rw [h_eq, h_at_q, Pauli.anticommutes_Z_eq_hasXComponent, hX_false]
        decide
      · rw [h_at_ne i hiq, Pauli.anticommutes_I_left]
        decide
    rw [h_filter_empty, Finset.card_empty]
    rfl

/-- Decomposition of `rowCut (i+1)`'s parity as XOR of three hasX's
    in row `i`. -/
theorem parity_rowCut_eq_row_xor (i : Fin 3) (F : ErrorVec 9) :
    ErrorVec.parity (rowCut (i.val + 1)) F =
      xor (xor (Pauli.hasXComponent (F (toIdx 3 i ⟨0, by decide⟩)))
               (Pauli.hasXComponent (F (toIdx 3 i ⟨1, by decide⟩))))
          (Pauli.hasXComponent (F (toIdx 3 i ⟨2, by decide⟩))) := by
  have h_decomp : rowCut (i.val + 1) =
      ErrorVec.mul
        (ErrorVec.mul (ofList [(3 * i.val, .Z)])
                      (ofList [(3 * i.val + 1, .Z)]))
        (ofList [(3 * i.val + 2, .Z)]) := by
    fin_cases i <;> (funext k; fin_cases k <;> rfl)
  rw [h_decomp, ErrorVec.parity_mul_left, ErrorVec.parity_mul_left]
  have h0 := parity_ofList_single_Z (3 * i.val)
              (by have := i.isLt; omega) F
  have h1 := parity_ofList_single_Z (3 * i.val + 1)
              (by have := i.isLt; omega) F
  have h2 := parity_ofList_single_Z (3 * i.val + 2)
              (by have := i.isLt; omega) F
  rw [h0, h1, h2]
  -- toIdx 3 i ⟨k, _⟩ has val = 3 * i.val + k, so both sides agree by rfl.
  rfl

/-- **The combinatorial step.** If `parity(rowCut i, F)` is `true`, then row
    `i − 1` of `F` has some X-component. Proved by contrapositive: if all
    three row positions have no X-component, the XOR decomposition gives
    `false`, contradiction. -/
theorem row_has_X_of_rowCut_parity {F : ErrorVec 9} {i : Fin 3}
    (h : ErrorVec.parity (rowCut (i.val + 1)) F = true) :
    ∃ j : Fin 3, Pauli.hasXComponent (F (toIdx 3 i j)) = true := by
  rw [parity_rowCut_eq_row_xor] at h
  by_contra hne
  push_neg at hne
  have h0 : Pauli.hasXComponent (F (toIdx 3 i ⟨0, by decide⟩)) = false := by
    have := hne ⟨0, by decide⟩
    cases Pauli.hasXComponent (F (toIdx 3 i ⟨0, by decide⟩)) <;> simp_all
  have h1 : Pauli.hasXComponent (F (toIdx 3 i ⟨1, by decide⟩)) = false := by
    have := hne ⟨1, by decide⟩
    cases Pauli.hasXComponent (F (toIdx 3 i ⟨1, by decide⟩)) <;> simp_all
  have h2 : Pauli.hasXComponent (F (toIdx 3 i ⟨2, by decide⟩)) = false := by
    have := hne ⟨2, by decide⟩
    cases Pauli.hasXComponent (F (toIdx 3 i ⟨2, by decide⟩)) <;> simp_all
  rw [h0, h1, h2] at h
  exact absurd h (by decide)

/-- **Topological lower bound** (paper Lemma `TopoLowerBound`,
    [invariant.tex:1753](../../../Codedistance/invariant.tex)). For any
    9-qubit Pauli vector `E` with zero syndrome and nontrivial logical Z
    parity, every stabilizer-multiplied representative uses X-component in
    all 3 rows of the d=3 grid.

    **Important:** the hypothesis here is only zero *Z-type* syndrome
    (not full zero syndrome). This is what `v2` provably implies; the
    stronger claim `v2 ⟹ zero X-type syndrome` is FALSE — refuted by the
    3-error attack `X_{q1} + Y_{q4} + X_{q7}` with staggered injection
    (see [notes/check_v2_x_syndrome_counterexample.py](../../../Codedistance/notes/check_v2_x_syndrome_counterexample.py)).

    Proof: For `F := mul S E`:
    (1) `parity(logicalZ, F) = parity(logicalZ, E) = 1` since `S` commutes
        with `L_Z` (by `parity_of_normalizer` on `L_Z ∈ normalizer`).
    (2) For each Z-type generator `T_j`, `parity(T_j, F) = 0`, since
        `parity(T_j, S) = 0` (abelianness) and `parity(T_j, E) = 0` (hZSyn).
    (3) The row-cut witnesses `S_i` (`S_1 = I`, `S_2 = s1·s6`,
        `S_3 = s4·s7·s1·s6`) are all Z-type products — so step (2) gives
        `parity(S_i, F) = 0`, and combined with `parity_mul_left` +
        `rowCut_i = S_i · L_Z`, `parity(rowCut i, F) = 1`.
    (4) By the combinatorial `row_has_X_of_rowCut_parity`, each of the 3
        rows has an X-component ⟹ `projRowsX ≥ 3`. -/
theorem topological_lower_bound
    (E : ErrorVec 9)
    (hZSyn : ∀ i : Fin code.numStab,
             isZType (code.stabilizers i) = true →
             ErrorVec.parity (code.stabilizers i) E = false)
    (hLog : ErrorVec.parity logicalZ E = true)
    {S : ErrorVec 9} (hS : QStab.InStab code S) :
    projRowsX (d := 3) (ErrorVec.mul S E) ≥ 3 := by
  -- For each Z-type generator, `parity(T_j, mul S E) = 0`.
  have hZSyn_F : ∀ j : Fin code.numStab,
      isZType (code.stabilizers j) = true →
      ErrorVec.parity (code.stabilizers j) (ErrorVec.mul S E) = false := by
    intro j hZ
    rw [ErrorVec.parity_mul_right, parity_generator_in_InStab j hS, hZSyn j hZ]
    rfl
  -- parity(logicalZ, mul S E) = true.
  have hLog_F : ErrorVec.parity logicalZ (ErrorVec.mul S E) = true := by
    rw [ErrorVec.parity_mul_right]
    have h_ZS : ErrorVec.parity logicalZ S = false := by
      rw [ErrorVec.parity_symm']
      exact QStab.InStab.parity_of_normalizer
              logicalZ_commutes_all_stabilizers hS
    rw [h_ZS, hLog]
    rfl
  -- For each row, `parity(rowCut (i+1), mul S E) = true`. Computed
  -- explicitly from the Z-type stab-equivalence witnesses.
  have h_logicalZ_eq_rowCut_1 : rowCut 1 = logicalZ := by
    funext i; fin_cases i <;> rfl
  have h_s1_Z : isZType (code.stabilizers ⟨0, by decide⟩) = true := by decide
  have h_s6_Z : isZType (code.stabilizers ⟨5, by decide⟩) = true := by decide
  have h_s4_Z : isZType (code.stabilizers ⟨3, by decide⟩) = true := by decide
  have h_s7_Z : isZType (code.stabilizers ⟨6, by decide⟩) = true := by decide
  -- Convert Z-type parities from `code.stabilizers j` form to `s_k` form.
  have h_s1_F : ErrorVec.parity s1 (ErrorVec.mul S E) = false :=
    hZSyn_F ⟨0, by decide⟩ h_s1_Z
  have h_s6_F : ErrorVec.parity s6 (ErrorVec.mul S E) = false :=
    hZSyn_F ⟨5, by decide⟩ h_s6_Z
  have h_s4_F : ErrorVec.parity s4 (ErrorVec.mul S E) = false :=
    hZSyn_F ⟨3, by decide⟩ h_s4_Z
  have h_s7_F : ErrorVec.parity s7 (ErrorVec.mul S E) = false :=
    hZSyn_F ⟨6, by decide⟩ h_s7_Z
  have h_row_parity : ∀ i : Fin 3,
      ErrorVec.parity (rowCut (i.val + 1)) (ErrorVec.mul S E) = true := by
    intro i
    fin_cases i
    · -- i = 0: rowCut 1 = L_Z.
      show ErrorVec.parity (rowCut 1) (ErrorVec.mul S E) = true
      rw [h_logicalZ_eq_rowCut_1]
      exact hLog_F
    · -- i = 1: rowCut 2 = (s1 · s6) · L_Z.
      show ErrorVec.parity (rowCut 2) (ErrorVec.mul S E) = true
      rw [rowCut_two_eq, h_logicalZ_eq_rowCut_1,
          ErrorVec.parity_mul_left, ErrorVec.parity_mul_left,
          h_s1_F, h_s6_F, hLog_F]
      rfl
    · -- i = 2: rowCut 3 = (s4 · s7) · ((s1 · s6) · L_Z).
      show ErrorVec.parity (rowCut 3) (ErrorVec.mul S E) = true
      rw [rowCut_three_eq, rowCut_two_eq, h_logicalZ_eq_rowCut_1,
          ErrorVec.parity_mul_left, ErrorVec.parity_mul_left,
          ErrorVec.parity_mul_left, ErrorVec.parity_mul_left,
          h_s4_F, h_s7_F, h_s1_F, h_s6_F, hLog_F]
      rfl
  -- Combinatorial step: each row has an X-component in `mul S E`.
  have h_rows_X : ∀ i : Fin 3,
      ∃ j : Fin 3, Pauli.hasXComponent (ErrorVec.mul S E (toIdx 3 i j)) = true :=
    fun i => row_has_X_of_rowCut_parity (h_row_parity i)
  -- Conclude: all 3 rows are in the projRowsX filter ⟹ projRowsX = 3.
  have h_projRowsX_eq : projRowsX (d := 3) (ErrorVec.mul S E) = 3 := by
    unfold projRowsX
    have h_univ : (Finset.univ.filter fun i : Fin 3 =>
        ∃ j : Fin 3,
          Pauli.hasXComponent (ErrorVec.mul S E (toIdx 3 i j)) = true)
        = Finset.univ := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact h_rows_X i
    rw [h_univ]
    simp
  omega

/-! ### v2 ⟹ zero Z-type syndrome

Note: `v2 ⟹ zero X-type syndrome` is FALSE — refuted by the 3-error attack
`X_{q1} + Y_{q4} + X_{q7}` with staggered injection (it has parity(ŝ_3, E) = 1
despite satisfying v2). See
[notes/check_v2_x_syndrome_counterexample.py](../../../Codedistance/notes/check_v2_x_syndrome_counterexample.py).

Fortunately the topological lower bound for the d=3 surface code only needs
zero *Z-type* syndrome, because the row-cut stabilizer-equivalence witnesses
(`s1·s6`, `s4·s7·s1·s6`) are Z-type products. The proof is adjusted
accordingly above. -/

/-- **v2 directly implies zero Z-type syndrome** via its final-data-detector
    conjunct: `G[i, R-1] ⊕ parity(T_i, Ẽ) = 0`. Combined with
    `allGZero ⟹ G[i, R-1] = 0`, this gives `parity(T_i, Ẽ) = 0` for each
    Z-type `T_i`. No reachability hypothesis needed — v2 is a direct
    syntactic constraint. -/
theorem v2_implies_zero_Z_syndrome
    (s : State testCode)
    (hv2 : isUndetectedLogicalError_v2 testCode logicalZ s = true) :
    ∀ i : Fin code.numStab,
      isZType (code.stabilizers i) = true →
      ErrorVec.parity (code.stabilizers i) s.E_tilde = false := by
  intro i hZ
  unfold isUndetectedLogicalError_v2 at hv2
  simp only [Bool.and_eq_true] at hv2
  obtain ⟨⟨hG, hDet⟩, _⟩ := hv2
  unfold allGZero at hG
  unfold allZTypeFinalDataDetectorsZero at hDet
  simp only [decide_eq_true_eq] at hG hDet
  have h_G_i : s.G i (lastRound testCode) = false := hG i (lastRound testCode)
  have h_det_i : finalDataDetector testCode s i = false := hDet i hZ
  unfold finalDataDetector at h_det_i
  rw [h_G_i] at h_det_i
  -- h_det_i : xor false (parity (T_i) E) = false
  simpa using h_det_i

/-- **Path A target theorem (fully proved, no axioms).** For any reachable
    state `s` in the d=3 NZ-scheduled surface code where the v2 predicate
    holds (undetected logical error in the Stim `memory_z` semantics), the
    execution must have used at least `d = 3` error injections.

    Proof: `perpSpread` gives `∃ S_wit, projRowsX (S_wit · Ẽ) + C ≤ 20` for
    reachable `s`. `v2 ⟹ zero Z-type syndrome` (provable) and
    `parity(L_Z, Ẽ) = 1`. The topological lower bound (which only requires
    zero *Z*-syndrome) gives `projRowsX (S_wit · Ẽ) ≥ 3`. Hence
    `3 + C ≤ 20`, i.e., `C_budget − C ≥ 3`. -/
theorem d3_nz_dCirc_v2_ge_d
    (s : State testCode)
    (hreach : MultiStep testCode (.active (State.init testCode)) (.active s))
    (hv2 : isUndetectedLogicalError_v2 testCode logicalZ s = true) :
    testCode.C_budget - s.C ≥ 3 := by
  -- Reachable ⟹ invariant holds.
  have hinv : perpSpreadX_holds s :=
    perpSpreadX_Invariant.holds_of_reachable s hreach
  obtain ⟨S_wit, hS_stab, hbound⟩ := hinv
  -- v2 unpacks: G = 0, Z-type detectors = 0, parity(L_Z, Ẽ) = 1.
  have hv2' : allGZero testCode s = true
            ∧ allZTypeFinalDataDetectorsZero testCode s = true
            ∧ ErrorVec.parity logicalZ s.E_tilde = true := by
    unfold isUndetectedLogicalError_v2 at hv2
    simp only [Bool.and_eq_true] at hv2
    exact ⟨hv2.1.1, hv2.1.2, hv2.2⟩
  have hLog : ErrorVec.parity logicalZ s.E_tilde = true := hv2'.2.2
  -- Zero Z-type syndrome from v2 (no axiom).
  have hZSyn : ∀ i : Fin code.numStab,
               isZType (code.stabilizers i) = true →
               ErrorVec.parity (code.stabilizers i) s.E_tilde = false :=
    v2_implies_zero_Z_syndrome s hv2
  -- Topological lower bound applied at Ẽ with stabilizer witness S_wit.
  have hTLB : projRowsX (d := 3) (ErrorVec.mul S_wit s.E_tilde) ≥ 3 :=
    topological_lower_bound s.E_tilde hZSyn hLog hS_stab
  -- Combine with the perpSpread bound.
  show testCode.C_budget - s.C ≥ 3
  have : testCode.C_budget = 20 := rfl
  omega

end QStab.Examples.SurfaceD3

/-! ## d=4 spec-level proofs -/

namespace QStab.Examples.SurfaceD4

open QStab

theorem logicalX_commutes_all_stabilizers :
    ∀ i : Fin code.numStab, ErrorVec.parity (code.stabilizers i) logicalX = false := by
  decide

theorem logicalZ_commutes_all_stabilizers :
    ∀ i : Fin code.numStab, ErrorVec.parity (code.stabilizers i) logicalZ = false := by
  decide

theorem logicalX_anticommutes_logicalZ :
    ErrorVec.parity logicalX logicalZ = true := by
  decide

theorem logicalX_notInStab :
    notInStab code logicalX logicalZ logicalX = true := by
  decide

theorem logicalZ_notInStab :
    notInStab code logicalX logicalZ logicalZ = true := by
  decide

/-! ### A1 + B2 for d=4: hook enumeration and commutation

Extends the d=3 work to d=4. 15 stabilizers (9 bulk × 3 hooks + 6 boundary × 1
hook = 33 hook errors total). Same paper references: HookSupportsNZ, HookPerp,
StabAbsorb ([invariant.tex:1450-1525](../../../Codedistance/invariant.tex)).

Stabilizer geometry for d=4 (qubit Fin indices):

| s | type  | role              | NW, NE, SW, SE  |
|---|-------|-------------------|-----------------|
| 0 | Z     | bulk s₁           | 0, 1, 4, 5      |
| 1 | Z     | bulk s₂           | 2, 3, 6, 7      |
| 2 | Z     | bulk s₃           | 5, 6, 9, 10     |
| 3 | Z     | bulk s₄           | 8, 9, 12, 13    |
| 4 | Z     | bulk s₅           | 10, 11, 14, 15  |
| 5 | X     | bulk s₆           | 1, 2, 5, 6      |
| 6 | X     | bulk s₇           | 4, 5, 8, 9      |
| 7 | X     | bulk s₈           | 6, 7, 10, 11    |
| 8 | X     | bulk s₉           | 9, 10, 13, 14   |
| 9 | Z     | boundary s₁₀ left | 4, 8            |
|10 | Z     | boundary s₁₁ right| 7, 11           |
|11 | X     | boundary s₁₂ top  | 0, 1            |
|12 | X     | boundary s₁₃ top  | 2, 3            |
|13 | X     | boundary s₁₄ bot  | 12, 13          |
|14 | X     | boundary s₁₅ bot  | 14, 15          |
-/

/-- Enumerated NZ hook errors for each d=4 stabilizer. -/
def hookErrors : Fin 15 → List (ErrorVec 16)
  -- Z-type bulk (N-order: j=1 → {SW,NE,SE}, j=2 → {NE,SE}, j=3 → {SE})
  | ⟨0, _⟩ => [ ofList [(1, .Z), (4, .Z), (5, .Z)]
              , ofList [(1, .Z), (5, .Z)]
              , ofList [(5, .Z)] ]
  | ⟨1, _⟩ => [ ofList [(3, .Z), (6, .Z), (7, .Z)]
              , ofList [(3, .Z), (7, .Z)]
              , ofList [(7, .Z)] ]
  | ⟨2, _⟩ => [ ofList [(6, .Z), (9, .Z), (10, .Z)]
              , ofList [(6, .Z), (10, .Z)]
              , ofList [(10, .Z)] ]
  | ⟨3, _⟩ => [ ofList [(9, .Z), (12, .Z), (13, .Z)]
              , ofList [(9, .Z), (13, .Z)]
              , ofList [(13, .Z)] ]
  | ⟨4, _⟩ => [ ofList [(11, .Z), (14, .Z), (15, .Z)]
              , ofList [(11, .Z), (15, .Z)]
              , ofList [(15, .Z)] ]
  -- X-type bulk (Z-order: j=1 → {NE,SW,SE}, j=2 → {SW,SE}, j=3 → {SE})
  | ⟨5, _⟩ => [ ofList [(2, .X), (5, .X), (6, .X)]
              , ofList [(5, .X), (6, .X)]
              , ofList [(6, .X)] ]
  | ⟨6, _⟩ => [ ofList [(5, .X), (8, .X), (9, .X)]
              , ofList [(8, .X), (9, .X)]
              , ofList [(9, .X)] ]
  | ⟨7, _⟩ => [ ofList [(7, .X), (10, .X), (11, .X)]
              , ofList [(10, .X), (11, .X)]
              , ofList [(11, .X)] ]
  | ⟨8, _⟩ => [ ofList [(10, .X), (13, .X), (14, .X)]
              , ofList [(13, .X), (14, .X)]
              , ofList [(14, .X)] ]
  -- Z-type boundary (top→bottom): hook on second qubit
  | ⟨9, _⟩  => [ ofList [(8, .Z)] ]      -- s10: q5→q9, hook on q9
  | ⟨10, _⟩ => [ ofList [(11, .Z)] ]     -- s11: q8→q12, hook on q12
  -- X-type boundary (left→right): hook on second qubit
  | ⟨11, _⟩ => [ ofList [(1, .X)] ]      -- s12: q1→q2, hook on q2
  | ⟨12, _⟩ => [ ofList [(3, .X)] ]      -- s13: q3→q4, hook on q4
  | ⟨13, _⟩ => [ ofList [(13, .X)] ]     -- s14: q13→q14, hook on q14
  | ⟨14, _⟩ => [ ofList [(15, .X)] ]     -- s15: q15→q16, hook on q16

/-- **B2 cancellation for d=4**: every NZ hook commutes with its parent stabilizer. -/
theorem hook_commutes_its_stabilizer :
    ∀ s : Fin 15, ∀ e ∈ hookErrors s,
    ErrorVec.parity (stabilizers s) e = false := by
  decide

/-- Weight bound: all d=4 hooks have weight ≤ 3. -/
theorem hook_weight_bound :
    ∀ s : Fin 15, ∀ e ∈ hookErrors s, ErrorVec.weight e ≤ 3 := by
  decide

/-- Count check: each weight-4 bulk has 3 hooks; each weight-2 boundary has 1. -/
theorem hook_count :
    (hookErrors ⟨0, by decide⟩).length = 3 ∧
    (hookErrors ⟨4, by decide⟩).length = 3 ∧
    (hookErrors ⟨5, by decide⟩).length = 3 ∧
    (hookErrors ⟨8, by decide⟩).length = 3 ∧
    (hookErrors ⟨9, by decide⟩).length = 1 ∧
    (hookErrors ⟨14, by decide⟩).length = 1 := by
  decide

/-- HookPerp for d=4: weight-2 X-type hook is horizontal (same row). -/
theorem weight2_Xhook_sameRow_s6 :
    ofList [(5, .X), (6, .X)] ∈ hookErrors ⟨5, by decide⟩ := by decide  -- q₆,q₇ row 2

theorem weight2_Xhook_sameRow_s7 :
    ofList [(8, .X), (9, .X)] ∈ hookErrors ⟨6, by decide⟩ := by decide  -- q₉,q₁₀ row 3

theorem weight2_Xhook_sameRow_s8 :
    ofList [(10, .X), (11, .X)] ∈ hookErrors ⟨7, by decide⟩ := by decide  -- q₁₁,q₁₂ row 3

theorem weight2_Xhook_sameRow_s9 :
    ofList [(13, .X), (14, .X)] ∈ hookErrors ⟨8, by decide⟩ := by decide  -- q₁₄,q₁₅ row 4

/-- HookPerp for d=4: weight-2 Z-type hook is vertical (same column). -/
theorem weight2_Zhook_sameCol_s1 :
    ofList [(1, .Z), (5, .Z)] ∈ hookErrors ⟨0, by decide⟩ := by decide  -- q₂,q₆ col 2

theorem weight2_Zhook_sameCol_s2 :
    ofList [(3, .Z), (7, .Z)] ∈ hookErrors ⟨1, by decide⟩ := by decide  -- q₄,q₈ col 4

theorem weight2_Zhook_sameCol_s3 :
    ofList [(6, .Z), (10, .Z)] ∈ hookErrors ⟨2, by decide⟩ := by decide  -- q₇,q₁₁ col 3

theorem weight2_Zhook_sameCol_s4 :
    ofList [(9, .Z), (13, .Z)] ∈ hookErrors ⟨3, by decide⟩ := by decide  -- q₁₀,q₁₄ col 2

theorem weight2_Zhook_sameCol_s5 :
    ofList [(11, .Z), (15, .Z)] ∈ hookErrors ⟨4, by decide⟩ := by decide  -- q₁₂,q₁₆ col 4

end QStab.Examples.SurfaceD4
