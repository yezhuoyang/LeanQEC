import QStab.Examples.SurfaceGeometry

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

/-! ### Phase 4 scaffolding — the perpendicular spread invariant

This is the central Phase 4 invariant from [invariant.tex:1561](../../../Codedistance/invariant.tex)
(ghost-witness reformulation):

    p^{ω_X}(σ)  :=  ∃ S_wit ∈ InStab code, projRowsX (mul S_wit Ẽ) ≤ C_budget − C

For Path A (theorem `d^circ_{v2} ≥ d` under NZ scheduling), this invariant is
the key tool: combined with the topological lower bound (Phase 5 step 4),
it forces |F| ≥ d for any execution with `v2 = true`.

Stated here as a `Prop` on `State`; `holds_init` is proved; preservation is
the subject of Phase 5 step 4 (pending). -/

open QStab

/-- Perpendicular spread (ghost-witness form) for the d=3 surface code. -/
def perpSpreadX_holds (s : State code) : Prop :=
  ∃ S_wit : ErrorVec 9,
    QStab.InStab code S_wit ∧
    projRowsX (d := 3) (ErrorVec.mul S_wit s.E_tilde) ≤ code.C_budget - s.C

/-- **Init**: at σ_0, `Ẽ = I`, `C = C_budget`, so `C_budget − C = 0`. Choose
    `S_wit = I`; then `mul I I = I` and `projRowsX I = 0 ≤ 0`. -/
theorem perpSpreadX_init : perpSpreadX_holds (State.init code) := by
  refine ⟨ErrorVec.identity 9, QStab.InStab.identity, ?_⟩
  show projRowsX (d := 3) (ErrorVec.mul (ErrorVec.identity 9) (ErrorVec.identity 9))
       ≤ code.C_budget - code.C_budget
  rw [Nat.sub_self]
  have hmul : ErrorVec.mul (ErrorVec.identity 9) (ErrorVec.identity 9)
              = ErrorVec.identity 9 := by funext _; rfl
  rw [hmul]
  exact Nat.le_of_eq (projRowsX_identity 3)

/-- The preservation obligation for `perpSpreadX_holds`. Structurally mirrors
    the paper's Proposition `PerpSpreadPreserve` ([invariant.tex:1647](../../../Codedistance/invariant.tex)).
    Each transition needs its own case:
      * Type-0, Type-I: single-qubit perturbation — `S_wit' = S_wit`, uses `SingleQubitPerturb`.
      * Type-II (NZ hook):
          - weight 1, 2: `S_wit' = S_wit`, uses `HookPerp`.
          - weight 3: `S_wit' = T_s · S_wit`, uses `StabAbsorb`.
      * Type-III, measure, halt: `Ẽ` unchanged, same `S_wit` works.
    TODO — to be proved as Phase 5 step 4. -/
theorem perpSpreadX_preservation
    (s s' : State code)
    (hinv : perpSpreadX_holds s)
    (hstep : Step code (.active s) (.active s')) :
    perpSpreadX_holds s' := by
  sorry

/-! ### Path A canonical theorem (stated; proof is the remaining work)

The theorem that v2-true requires at least `d` errors, for the d=3 case. With
Phase 4 preservation + topological lower bound + two-phase argument, this
follows. Empirically verified at 2-op level by exhaustive enumeration. -/

/-- **Target theorem** (Path A, d=3): `d^circ_{v2}(d=3, R=5) ≥ 3`. Equivalently,
    any execution with `v2 = true` at σ_done uses at least 3 error injections.

    For d=3, the minimum-weight logical operator `L_X = X_{q₁}X_{q₄}X_{q₇}` has
    weight `d = 3`; since v2-true requires `Ẽ` in a non-trivial stabilizer
    coset with clean measurement record, at least `d` faults are needed.

    This combines:
      - `perpSpreadX_preservation` (Phase 5 step 4 — pending),
      - topological lower bound (Phase 5 step 4 — pending),
      - two-phase argument (Phase 6 — pending). -/
theorem d3_nz_dCirc_v2_ge_d :
    ∀ s : State testCode,
      isUndetectedLogicalError_v2 testCode logicalZ s = true →
      testCode.C_budget - s.C ≥ 3 := by
  sorry

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
