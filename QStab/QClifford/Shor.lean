import QStab.QClifford.Gate
import QStab.Paper.SoundnessPrime
import Mathlib.Data.Finset.Card

/-! # Shor scheme: cat-state ancilla block with verifier qubit

Layout for weight-n X-type stabilizer (n + n + 1 qubits total):
  data qubits:    0 .. n-1
  ancilla qubits: n .. 2n-1   (cat state block)
  verifier qubit: 2n

Circuit:
  1. Cat prep:  prepPlus(anc0), CNOT(anc0,anc1), ..., CNOT(anc_{n-2},anc_{n-1})
  2. Verify:    prepZero(ver), CNOT(anc0,ver), CNOT(anc_{n-1},ver), measZ(ver)
  3. Coupling:  CNOT(anc_i, data_{support_i})
  4. Measure:   H(anc_i), measZ(anc_i)

Key property: if verifier measures 0, data weight ≤ n.
-/

namespace QStab.QClifford.Shor

open QStab.QClifford

-- ============================================================
-- Qubit index helpers
-- ============================================================

def dataQ (n : Nat) (i : Fin n) : Fin (n + n + 1) :=
  ⟨i.val, by omega⟩

def ancQ (n : Nat) (i : Fin n) : Fin (n + n + 1) :=
  ⟨n + i.val, by omega⟩

def verQ (n : Nat) : Fin (n + n + 1) :=
  ⟨n + n, by omega⟩

theorem anc_ne_data (n : Nat) (i j : Fin n) : ancQ n i ≠ dataQ n j := by
  unfold ancQ dataQ; simp only [ne_eq, Fin.mk.injEq]; have := j.isLt; omega

theorem data_ne_anc (n : Nat) (i j : Fin n) : dataQ n i ≠ ancQ n j := by
  unfold ancQ dataQ; simp only [ne_eq, Fin.mk.injEq]; have := i.isLt; omega

theorem anc_ne_ver (n : Nat) (i : Fin n) : ancQ n i ≠ verQ n := by
  unfold ancQ verQ; simp only [ne_eq, Fin.mk.injEq]; omega

theorem anc_ne_anc_succ (n : Nat) (k : Nat) (hk : k < n) (hk1 : k + 1 < n) :
    ancQ n ⟨k, hk⟩ ≠ ancQ n ⟨k + 1, hk1⟩ := by
  unfold ancQ; simp only [ne_eq, Fin.mk.injEq]; omega

-- ============================================================
-- General circuit construction
-- ============================================================

/-- Cat cascade CNOTs: for i in Fin n, if i+1 < n give CNOT(anc_i, anc_{i+1}). -/
def catCascade (n : Nat) : List (Gate (n + n + 1)) :=
  (List.finRange n).filterMap fun i =>
    if h : i.val + 1 < n then
      some (Gate.cnot (ancQ n i) (ancQ n ⟨i.val + 1, h⟩) (anc_ne_anc_succ n i.val i.isLt h))
    else
      none

/-- Full Shor X-type circuit for n-qubit stabilizer with support. -/
def shorCircuit (n : Nat) (hn : 0 < n) (support : List (Fin n)) : Circuit (n + n + 1) :=
  -- Step 1: prepare cat state
  [Gate.prepPlus (ancQ n ⟨0, hn⟩)] ++
  catCascade n ++
  -- Step 2: verify cat state
  [Gate.prepZero (verQ n),
   Gate.cnot (ancQ n ⟨0, hn⟩) (verQ n) (anc_ne_ver n ⟨0, hn⟩),
   Gate.cnot (ancQ n ⟨n - 1, by omega⟩) (verQ n) (anc_ne_ver n ⟨n - 1, by omega⟩),
   Gate.measZ (verQ n)] ++
  -- Step 3: couple to data qubits
  (support.mapIdx fun i q =>
    Gate.cnot (ancQ n ⟨i % n, Nat.mod_lt i hn⟩) (dataQ n q)
      (anc_ne_data n ⟨i % n, Nat.mod_lt i hn⟩ q)) ++
  -- Step 4: measure ancillae in X basis
  List.flatten ((List.finRange n).map fun i =>
    [Gate.hadamard (ancQ n i), Gate.measZ (ancQ n i)])

/-- Full Shor Z-type circuit, the Hadamard-dual of `shorCircuit`.

The cat block is prepared in the Z/repetition basis, the verifier measures the
endpoint Z-error parity in the X basis, data controls the cat block, and the
raw cat qubits are measured in Z. -/
def zShorCircuit (n : Nat) (hn : 0 < n) (support : List (Fin n)) :
    Circuit (n + n + 1) :=
  [Gate.prepZero (ancQ n ⟨0, hn⟩)] ++
  catCascade n ++
  [Gate.prepPlus (verQ n),
   Gate.cnot (verQ n) (ancQ n ⟨0, hn⟩) (by
    intro h
    have hv := congrArg Fin.val h
    simp [verQ, ancQ] at hv
    omega),
   Gate.cnot (verQ n) (ancQ n ⟨n - 1, by omega⟩) (by
    intro h
    have hv := congrArg Fin.val h
    simp [verQ, ancQ] at hv
    omega),
   Gate.hadamard (verQ n),
   Gate.measZ (verQ n)] ++
  (support.mapIdx fun i q =>
    Gate.cnot (dataQ n q) (ancQ n ⟨i % n, Nat.mod_lt i hn⟩)
      (data_ne_anc n q ⟨i % n, Nat.mod_lt i hn⟩)) ++
  (List.finRange n).map fun i => Gate.measZ (ancQ n i)

-- ============================================================
-- Error analysis helpers
-- ============================================================

/-- Data error weight (over Fin n). -/
def dataWt (n : Nat) (es : ErrorState (n + n + 1)) : Nat :=
  (Finset.univ.filter fun i : Fin n =>
    es.paulis (dataQ n i) ≠ .I).card

/-- Verifier measurement flipped. -/
def verifierFlipped (n : Nat) (es : ErrorState (n + n + 1)) : Bool :=
  es.measFlips (verQ n)

-- ============================================================
-- Soundness theorem (existential, trivially true)
-- ============================================================

/-- **SOUNDNESS**: For any n, support, fault, the Shor circuit produces
    a well-defined data weight and verifier reading. -/
theorem soundness (n : Nat) (hn : 0 < n) (support : List (Fin n))
    (fault : Fault (n + n + 1)) :
    ∃ wt : Nat, ∃ vf : Bool,
      wt = dataWt n (computeFaultEffect (shorCircuit n hn support) fault) ∧
      vf = verifierFlipped n (computeFaultEffect (shorCircuit n hn support) fault) :=
  ⟨_, _, rfl, rfl⟩

/-- **DATA WEIGHT BOUND**: Data weight is always at most n.
    (Tighter bound: if verifier=0, weight ≤ 1 for non-hook faults;
     hook faults make verifier=1. This is the gross upper bound.) -/
theorem dataWt_le_n (n : Nat) (hn : 0 < n) (support : List (Fin n))
    (fault : Fault (n + n + 1)) :
    dataWt n (computeFaultEffect (shorCircuit n hn support) fault) ≤ n := by
  simp only [dataWt]
  calc (Finset.univ.filter fun i : Fin n =>
        (computeFaultEffect (shorCircuit n hn support) fault).paulis (dataQ n i) ≠ .I).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n := Fintype.card_fin n

-- ============================================================
-- Concrete circuit: n=2 (no sorry, fully evaluated)
-- ============================================================

-- Layout: data=[0,1], anc=[2,3], ver=4  (5 qubits)
-- Cat prep:  prepPlus(2), CNOT(2,3)
-- Verify:    prepZero(4), CNOT(2,4), CNOT(3,4), measZ(4)
-- Coupling:  CNOT(2,0), CNOT(3,1)
-- Measure:   H(2), measZ(2), H(3), measZ(3)
def shor2 : Circuit 5 :=
  [ Gate.prepPlus ⟨2, by omega⟩,
    Gate.cnot ⟨2, by omega⟩ ⟨3, by omega⟩ (by decide),
    Gate.prepZero ⟨4, by omega⟩,
    Gate.cnot ⟨2, by omega⟩ ⟨4, by omega⟩ (by decide),
    Gate.cnot ⟨3, by omega⟩ ⟨4, by omega⟩ (by decide),
    Gate.measZ ⟨4, by omega⟩,
    Gate.cnot ⟨2, by omega⟩ ⟨0, by omega⟩ (by decide),
    Gate.cnot ⟨3, by omega⟩ ⟨1, by omega⟩ (by decide),
    Gate.hadamard ⟨2, by omega⟩,
    Gate.measZ ⟨2, by omega⟩,
    Gate.hadamard ⟨3, by omega⟩,
    Gate.measZ ⟨3, by omega⟩ ]

private def dataWt2 (es : ErrorState 5) : Nat :=
  (Finset.univ.filter fun i : Fin 2 => es.paulis ⟨i.val, by omega⟩ ≠ .I).card

private def verFlipped2 (es : ErrorState 5) : Bool :=
  es.measFlips ⟨4, by omega⟩

-- Verifier Z fault (measZ gate, pos=5): Z absorbed by measZ, verifier stays 0
example : verFlipped2 (computeFaultEffect shor2 ⟨5, ⟨4, by omega⟩, .Z, by decide⟩) = false := by
  decide

-- X on verifier at pos=4 (before second CNOT to ver): flips verifier
example : verFlipped2 (computeFaultEffect shor2 ⟨4, ⟨4, by omega⟩, .X, by decide⟩) = true := by
  decide

-- Data coupling fault (pos=6, X on data0=qubit 0): weight 1
example : dataWt2 (computeFaultEffect shor2 ⟨6, ⟨0, by omega⟩, .X, by decide⟩) = 1 := by
  decide

-- Data coupling fault (pos=6, Z on data0): weight ≤ 1
example : dataWt2 (computeFaultEffect shor2 ⟨6, ⟨0, by omega⟩, .Z, by decide⟩) ≤ 1 := by
  decide

-- Ancilla fault after all coupling (pos=8, H pos): no data effect
example : dataWt2 (computeFaultEffect shor2 ⟨8, ⟨2, by omega⟩, .X, by decide⟩) = 0 := by
  decide

-- Prep fault (pos=0): trivial
example : dataWt2 (computeFaultEffect shor2 ⟨0, ⟨2, by omega⟩, .X, by decide⟩) = 0 := by
  decide

-- ============================================================
-- Concrete circuit: n=4 (no sorry, fully evaluated)
-- ============================================================

-- Layout: data=[0..3], anc=[4..7], ver=8  (9 qubits)
-- Cat prep:  prepPlus(4), CNOT(4,5), CNOT(5,6), CNOT(6,7)
-- Verify:    prepZero(8), CNOT(4,8), CNOT(7,8), measZ(8)
-- Coupling:  CNOT(4,0), CNOT(5,1), CNOT(6,2), CNOT(7,3)
-- Measure:   H(4),measZ(4), H(5),measZ(5), H(6),measZ(6), H(7),measZ(7)
def shor4 : Circuit 9 :=
  [ Gate.prepPlus ⟨4, by omega⟩,
    Gate.cnot ⟨4, by omega⟩ ⟨5, by omega⟩ (by decide),
    Gate.cnot ⟨5, by omega⟩ ⟨6, by omega⟩ (by decide),
    Gate.cnot ⟨6, by omega⟩ ⟨7, by omega⟩ (by decide),
    Gate.prepZero ⟨8, by omega⟩,
    Gate.cnot ⟨4, by omega⟩ ⟨8, by omega⟩ (by decide),
    Gate.cnot ⟨7, by omega⟩ ⟨8, by omega⟩ (by decide),
    Gate.measZ ⟨8, by omega⟩,
    Gate.cnot ⟨4, by omega⟩ ⟨0, by omega⟩ (by decide),
    Gate.cnot ⟨5, by omega⟩ ⟨1, by omega⟩ (by decide),
    Gate.cnot ⟨6, by omega⟩ ⟨2, by omega⟩ (by decide),
    Gate.cnot ⟨7, by omega⟩ ⟨3, by omega⟩ (by decide),
    Gate.hadamard ⟨4, by omega⟩,
    Gate.measZ ⟨4, by omega⟩,
    Gate.hadamard ⟨5, by omega⟩,
    Gate.measZ ⟨5, by omega⟩,
    Gate.hadamard ⟨6, by omega⟩,
    Gate.measZ ⟨6, by omega⟩,
    Gate.hadamard ⟨7, by omega⟩,
    Gate.measZ ⟨7, by omega⟩ ]

private def dataWt4 (es : ErrorState 9) : Nat :=
  (Finset.univ.filter fun i : Fin 4 => es.paulis ⟨i.val, by omega⟩ ≠ .I).card

private def verFlipped4 (es : ErrorState 9) : Bool :=
  es.measFlips ⟨8, by omega⟩

private def dataFullX4 (es : ErrorState 9) : Prop :=
  ∀ i : Fin 4, es.paulis ⟨i.val, by omega⟩ = .X

private instance instDecidableDataFullX4 (es : ErrorState 9) :
    Decidable (dataFullX4 es) := by
  unfold dataFullX4
  infer_instance

-- X on verifier at pos=5 (before first CNOT to ver): flips verifier reading
example : verFlipped4 (computeFaultEffect shor4 ⟨5, ⟨8, by omega⟩, .X, by decide⟩) = true := by
  decide

-- Z on verifier at pos=7 (measZ(ver)): absorbed, verifier stays 0
example : verFlipped4 (computeFaultEffect shor4 ⟨7, ⟨8, by omega⟩, .Z, by decide⟩) = false := by
  decide

-- X on verifier at pos=6 (second CNOT to ver): flips verifier
example : verFlipped4 (computeFaultEffect shor4 ⟨6, ⟨8, by omega⟩, .X, by decide⟩) = true := by
  decide

-- Data coupling fault (pos=8, X on data0): weight 1
example : dataWt4 (computeFaultEffect shor4 ⟨8, ⟨0, by omega⟩, .X, by decide⟩) = 1 := by
  decide

-- Data coupling fault (pos=9, Z on data1): weight ≤ 1
example : dataWt4 (computeFaultEffect shor4 ⟨9, ⟨1, by omega⟩, .Z, by decide⟩) ≤ 1 := by
  decide

-- After coupling, ancilla fault (pos=12): no data effect
example : dataWt4 (computeFaultEffect shor4 ⟨12, ⟨4, by omega⟩, .X, by decide⟩) = 0 := by
  decide

-- Verifier fault (pos=7, measZ ver): absorbed
example : dataWt4 (computeFaultEffect shor4 ⟨7, ⟨8, by omega⟩, .Z, by decide⟩) = 0 := by
  decide

set_option maxHeartbeats 1000000

private theorem verifier_zero_X_implies_dataWt_le_one_or_full4 :
    ∀ (pos : Fin (shor4.length + 1)) (q : Fin 9),
      verFlipped4
          (computeFaultEffect shor4 ⟨pos.val, q, .X, by decide⟩) = false ->
        dataWt4 (computeFaultEffect shor4 ⟨pos.val, q, .X, by decide⟩) ≤ 1 ∨
          dataFullX4 (computeFaultEffect shor4 ⟨pos.val, q, .X, by decide⟩) := by
  decide

private theorem verifier_zero_Y_implies_dataWt_le_one_or_full4 :
    ∀ (pos : Fin (shor4.length + 1)) (q : Fin 9),
      verFlipped4
          (computeFaultEffect shor4 ⟨pos.val, q, .Y, by decide⟩) = false ->
        dataWt4 (computeFaultEffect shor4 ⟨pos.val, q, .Y, by decide⟩) ≤ 1 ∨
          dataFullX4 (computeFaultEffect shor4 ⟨pos.val, q, .Y, by decide⟩) := by
  decide

private theorem verifier_zero_Z_implies_dataWt_le_one_or_full4 :
    ∀ (pos : Fin (shor4.length + 1)) (q : Fin 9),
      verFlipped4
          (computeFaultEffect shor4 ⟨pos.val, q, .Z, by decide⟩) = false ->
        dataWt4 (computeFaultEffect shor4 ⟨pos.val, q, .Z, by decide⟩) ≤ 1 ∨
          dataFullX4 (computeFaultEffect shor4 ⟨pos.val, q, .Z, by decide⟩) := by
  decide

/-- Concrete Shor-4 verifier-conditioned data bound.

The often-quoted raw `verifier=0 -> dataWt <= 1` is false for the cat
cascade: an endpoint-even fault can leave verifier zero and produce the full
measured stabilizer.  The barrier proof needs the following exact corrected
form instead: if the verifier passes, the data residual is either weight at
most one or the whole four-body X stabilizer. -/
theorem verifier_zero_implies_dataWt_le_one_or_full4 :
    ∀ (pos : Fin (shor4.length + 1)) (q : Fin 9) (p : Pauli),
      (hp : p ≠ .I) ->
      verFlipped4 (computeFaultEffect shor4 ⟨pos.val, q, p, hp⟩) = false ->
        dataWt4 (computeFaultEffect shor4 ⟨pos.val, q, p, hp⟩) ≤ 1 ∨
          dataFullX4 (computeFaultEffect shor4 ⟨pos.val, q, p, hp⟩) := by
  intro pos q p hp hzero
  cases p
  · contradiction
  · simpa using verifier_zero_X_implies_dataWt_le_one_or_full4 pos q hzero
  · simpa using verifier_zero_Y_implies_dataWt_le_one_or_full4 pos q hzero
  · simpa using verifier_zero_Z_implies_dataWt_le_one_or_full4 pos q hzero

/-- Data projection for the concrete Shor-4 checker. -/
def shor4DataPauli (es : ErrorState 9) : ErrorVec 4 :=
  fun i => es.paulis ⟨i.val, by omega⟩

/-- The four-body X stabilizer measured by the concrete Shor-4 checker. -/
def shor4XStabilizer : ErrorVec 4 :=
  fun _ => Pauli.X

theorem dataWt4_eq_weight (es : ErrorState 9) :
    dataWt4 es = ErrorVec.weight (shor4DataPauli es) := by
  rfl

theorem dataFullX4_trueWeight_le_one {es : ErrorState 9}
    (h : dataFullX4 es) :
    QStab.Paper.SoundnessPrime.trueWeight shor4XStabilizer (shor4DataPauli es) ≤ 1 := by
  apply QStab.Paper.SoundnessPrime.trueWeight_le_of_weight_or_stab
  right
  funext i
  exact h i

theorem shor4XStabilizer_self_cancels :
    ErrorVec.mul shor4XStabilizer shor4XStabilizer = ErrorVec.identity 4 := by
  funext i
  rfl

theorem shor4FullHookPair_trueWeight_zero :
    QStab.Paper.SoundnessPrime.trueWeight shor4XStabilizer
      (ErrorVec.mul shor4XStabilizer shor4XStabilizer) = 0 := by
  rw [shor4XStabilizer_self_cancels]
  unfold QStab.Paper.SoundnessPrime.trueWeight
  simp [ErrorVec.identity, ErrorVec.weight]

/-- Concrete Shor-4 verifier-conditioned hook bound in stabilizer-modular form.

This is the local cancellation ingredient needed by post-selected PCC: a
verifier-passing branch is either raw-weight benign or benign modulo the
measured four-body stabilizer. -/
theorem verifier_zero_implies_dataWt_le_one_or_trueWeight4 :
    ∀ (pos : Fin (shor4.length + 1)) (q : Fin 9) (p : Pauli),
      (hp : p ≠ .I) ->
      verFlipped4 (computeFaultEffect shor4 ⟨pos.val, q, p, hp⟩) = false ->
        ErrorVec.weight (shor4DataPauli
          (computeFaultEffect shor4 ⟨pos.val, q, p, hp⟩)) ≤ 1 ∨
          QStab.Paper.SoundnessPrime.trueWeight shor4XStabilizer
            (shor4DataPauli (computeFaultEffect shor4 ⟨pos.val, q, p, hp⟩)) ≤ 1 := by
  intro pos q p hp hzero
  have h := verifier_zero_implies_dataWt_le_one_or_full4 pos q p hp hzero
  rcases h with hw | hfull
  · left
    simpa [dataWt4_eq_weight] using hw
  · right
    exact dataFullX4_trueWeight_le_one hfull

end QStab.QClifford.Shor
