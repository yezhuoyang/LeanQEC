import QStab.Compiler
import QStab.QClifford.Standard
import QStab.Paper.Bridge
import QStab.Paper.Soundness
import QStab.Compiler.SchemeCorrectStandard

/-! # QStab.Compiler.ToCircuit — single-stabilizer gate-level compilation

Session 2 / Phase A2 entry point. Provides
`toCircuitStabilizerX : (spec : CodeSpec) → Fin spec.numStab → Circuit (spec.n + 1)`
which produces the standard CNOT syndrome-extraction circuit
(`Standard.xCircuit`) for one X-stabilizer of `spec`.

## Design choice (iter A2)

`xCircuit n support : Circuit (n + 1)` operates on **n data qubits + 1
ancilla** at index `n`. Per-stabilizer compilation therefore uses one
shared ancilla slot. Multi-stabilizer composition (iter A4+) will run
each per-stabilizer gadget back-to-back, relying on the fact that each
gadget starts with `prepPlus`/`prepZero` on the ancilla, which resets
any leftover ancilla state.

The number of qubits in the compiled bundle is therefore `spec.n + 1`,
not `spec.n`. The existing `compileBundle` in
`QStab/Verifier/QCliffordBundle.lean` uses `nq := b.P.n`; that field
will be updated to `nq := b.P.n + 1` in Phase C (iter C1).

## Connection to `qstab_sound`

For each single-stabilizer compilation, `qstab_sound` (in
`Paper/Soundness.lean`) gives a fault-classification guarantee
**provided** the resulting circuit satisfies `SchemeCorrect`. We do not
yet prove `SchemeCorrect (toCircuitStabilizerX spec s) T_s r` — that is
the work of iters A3 (proving C1: parityFaithful), A4 (C2:
noBackAction), and the existing `Standard.weight_bounded` already
discharges C3. The statement-level corollary
`toCircuitStabilizerX_qstab_sound` here records the *contract* under
that future hypothesis.
-/

namespace QStab.Compiler

open QStab QStab.QClifford QStab.QClifford.Standard QStab.Paper QStab.Paper.Soundness
open QStab.Compiler.SchemeCorrectStandard

/-- The X-side syndrome-extraction circuit for stabilizer `s` of
    `spec`. Thin wrapper over `Standard.xCircuit` applied to the
    stabilizer's gate ordering. Ancilla is at qubit index `spec.n`. -/
def toCircuitStabilizerX (spec : CodeSpec) (s : Fin spec.numStab) :
    Circuit (spec.n + 1) :=
  xCircuit spec.n (spec.gateOrdering s)

/-- The Z-side syndrome-extraction circuit for stabilizer `s` of
    `spec`. Symmetric to `toCircuitStabilizerX` but with CNOTs reversed
    (data → ancilla). -/
def toCircuitStabilizerZ (spec : CodeSpec) (s : Fin spec.numStab) :
    Circuit (spec.n + 1) :=
  zCircuit spec.n (spec.gateOrdering s)

/-- **Length smoke-check (X-side)**: a single X-stabilizer's circuit
    has exactly `|gateOrdering s| + 3` gates — one `prepPlus`,
    `|gateOrdering|` CNOTs, one `hadamard`, one `measZ`. -/
theorem toCircuitStabilizerX_length (spec : CodeSpec) (s : Fin spec.numStab) :
    (toCircuitStabilizerX spec s).length = (spec.gateOrdering s).length + 3 := by
  unfold toCircuitStabilizerX xCircuit
  simp [List.length_append, List.length_map]

/-- **Length smoke-check (Z-side)**: similar but no `hadamard`, so
    `|gateOrdering s| + 2`. -/
theorem toCircuitStabilizerZ_length (spec : CodeSpec) (s : Fin spec.numStab) :
    (toCircuitStabilizerZ spec s).length = (spec.gateOrdering s).length + 2 := by
  unfold toCircuitStabilizerZ zCircuit
  simp [List.length_append, List.length_map]

/-- **Conditional fault-classification corollary (X-side)**: if the
    per-stabilizer circuit satisfies `SchemeCorrect` for measuring
    `T_s` with hook-weight bound `r`, then every single fault classifies
    via `paperType` into a QStab transition `matchesQStab`-compatible
    with the observed data error and measurement flip. This is
    `qstab_sound` instantiated at our `toCircuitStabilizerX`.

    The `SchemeCorrect` hypothesis is discharged in iters A3/A4
    (parityFaithful + noBackAction); C3 follows from
    `Standard.weight_bounded`. -/
theorem toCircuitStabilizerX_qstab_sound (spec : CodeSpec) (s : Fin spec.numStab)
    (r : Nat)
    (h_correct : SchemeCorrect (toCircuitStabilizerX spec s) (spec.stabilizers s) r)
    (fault : Fault (spec.n + 1)) :
    matchesQStab
      (paperType spec.n (computeFaultEffect (toCircuitStabilizerX spec s) fault))
      (dataPauli (computeFaultEffect (toCircuitStabilizerX spec s) fault))
      (measFlipped spec.n (computeFaultEffect (toCircuitStabilizerX spec s) fault))
    ∧
    (paperType spec.n (computeFaultEffect (toCircuitStabilizerX spec s) fault) = .type2 →
      ErrorVec.weight
        (dataPauli (computeFaultEffect (toCircuitStabilizerX spec s) fault)) ≤ r) :=
  qstab_sound (toCircuitStabilizerX spec s) (spec.stabilizers s) r h_correct fault

/-! ## Round assembly (iter A4)

A single measurement round runs every stabilizer's per-gadget circuit
back-to-back. Each gadget begins with `prepPlus`/`prepZero` on the
shared ancilla (qubit `spec.n`), so the ancilla is reset at the start
of every gadget independently of leftover state.

The X-side round and Z-side round are separated: a real CSS code
schedules them as two halves of a round (or alternates). We provide
both as flat list concatenations; multi-round composition (Phase A7+)
will sequence them per `spec.R`. -/

/-- One round of all X-side syndrome extractions, concatenated by
    stabilizer index `0, 1, ..., numStab-1`. -/
def toCircuitXRound (spec : CodeSpec) : Circuit (spec.n + 1) :=
  (List.finRange spec.numStab).flatMap (toCircuitStabilizerX spec)

/-- One round of all Z-side syndrome extractions. -/
def toCircuitZRound (spec : CodeSpec) : Circuit (spec.n + 1) :=
  (List.finRange spec.numStab).flatMap (toCircuitStabilizerZ spec)

/-- **Length lemma (X-side round)**: total gates = sum over stabilizers
    of `(|gateOrdering s| + 3)`. -/
theorem toCircuitXRound_length (spec : CodeSpec) :
    (toCircuitXRound spec).length =
      ((List.finRange spec.numStab).map
        fun s => (spec.gateOrdering s).length + 3).sum := by
  unfold toCircuitXRound
  rw [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro s _
  exact toCircuitStabilizerX_length spec s

/-- **Length lemma (Z-side round)**: total gates = sum over stabilizers
    of `(|gateOrdering s| + 2)`. -/
theorem toCircuitZRound_length (spec : CodeSpec) :
    (toCircuitZRound spec).length =
      ((List.finRange spec.numStab).map
        fun s => (spec.gateOrdering s).length + 2).sum := by
  unfold toCircuitZRound
  rw [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro s _
  exact toCircuitStabilizerZ_length spec s

/-! ## Multi-round assembly (iters A5–A7)

`spec.R` rounds of syndrome extraction, X-side and Z-side separately.
Multi-round just replicates the round circuit and flattens — between
rounds, every gadget's leading `prepPlus`/`prepZero` resets the ancilla,
so no inter-round bookkeeping is required.

CSS-code-aware composition (mix X-stab and Z-stab indices per real
protocol) is deferred to iter A8+ — current `CodeSpec` doesn't tag each
stabilizer X-or-Z, so `toCircuitX` produces every stabilizer's X-side
gadget (correct only when all stabilizers are intended X-type for the
purpose of compilation). A future field `stabType : Fin numStab → Bool`
on `CodeSpec` (or a parameter) will let us assemble a real CSS round. -/

/-- Full X-side circuit: `spec.R` rounds of all-stabilizer X-side
    syndrome extraction, concatenated. -/
def toCircuitX (spec : CodeSpec) : Circuit (spec.n + 1) :=
  (List.replicate spec.R (toCircuitXRound spec)).flatten

/-- Full Z-side circuit. -/
def toCircuitZ (spec : CodeSpec) : Circuit (spec.n + 1) :=
  (List.replicate spec.R (toCircuitZRound spec)).flatten

/-- **Multi-round length lemma (X)**: total gates = `spec.R * round-length`. -/
private theorem replicate_flatten_length {α} (n : Nat) (l : List α) :
    (List.replicate n l).flatten.length = n * l.length := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, List.length_append, ih,
        Nat.succ_mul, Nat.add_comm]

theorem toCircuitX_length (spec : CodeSpec) :
    (toCircuitX spec).length = spec.R * (toCircuitXRound spec).length :=
  replicate_flatten_length spec.R (toCircuitXRound spec)

theorem toCircuitZ_length (spec : CodeSpec) :
    (toCircuitZ spec).length = spec.R * (toCircuitZRound spec).length :=
  replicate_flatten_length spec.R (toCircuitZRound spec)

/-! ## Multi-gadget data preservation

Composes iter 31's `xCircuit_dataPauli_preserved` over `flatMap` and
`flatten . replicate` to give the full-circuit data-preservation
result needed by `compileCertificate`'s real `invHolds`/`preservation`
wiring (iters 33-34). -/

/-- Auxiliary: through any list of stabilizers compiled to X-side
    gadgets and concatenated, data Paulis are preserved. -/
theorem flatMap_xGadgets_data_preserved (spec : CodeSpec)
    (lst : List (Fin spec.numStab)) (es : ErrorState (spec.n + 1))
    (i : Fin spec.n) :
    (propagateCircuit (lst.flatMap (toCircuitStabilizerX spec)) es).paulis
      ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ =
    es.paulis ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
  induction lst generalizing es with
  | nil =>
    simp [List.flatMap, propagateCircuit]
  | cons s rest ih =>
    rw [show (s :: rest).flatMap (toCircuitStabilizerX spec) =
            toCircuitStabilizerX spec s ++ rest.flatMap (toCircuitStabilizerX spec)
        from rfl,
        propagateCircuit_append]
    have h_one := xCircuit_dataPauli_preserved (spec.gateOrdering s) es i
    -- h_one : prop (xCircuit ...) es .paulis i = es.paulis i
    -- toCircuitStabilizerX spec s = xCircuit spec.n (spec.gateOrdering s)
    rw [ih]
    exact h_one

/-- **One X-side round preserves data**. -/
theorem toCircuitXRound_data_preserved (spec : CodeSpec)
    (es : ErrorState (spec.n + 1)) (i : Fin spec.n) :
    (propagateCircuit (toCircuitXRound spec) es).paulis
      ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ =
    es.paulis ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
  unfold toCircuitXRound
  exact flatMap_xGadgets_data_preserved spec _ es i

/-- Auxiliary: replicate-flatten over rounds preserves data. -/
theorem replicate_round_data_preserved (spec : CodeSpec) (R : Nat)
    (es : ErrorState (spec.n + 1)) (i : Fin spec.n) :
    (propagateCircuit (List.replicate R (toCircuitXRound spec)).flatten es).paulis
      ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ =
    es.paulis ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
  induction R generalizing es with
  | zero => simp [List.replicate, List.flatten, propagateCircuit]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, propagateCircuit_append]
    rw [ih]
    exact toCircuitXRound_data_preserved spec es i

/-- **Full X-side circuit preserves data**: through `spec.R` rounds
    of all-stabilizer X-side syndrome extraction, the data qubits
    are unchanged regardless of input state. This is what
    `compileCertificate` needs to argue that `liftInvariant` is
    preserved by every gate in the compiled circuit. -/
theorem toCircuitX_data_preserved (spec : CodeSpec)
    (es : ErrorState (spec.n + 1)) (i : Fin spec.n) :
    (propagateCircuit (toCircuitX spec) es).paulis
      ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ =
    es.paulis ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
  unfold toCircuitX
  exact replicate_round_data_preserved spec spec.R es i

/-! ## **Single-gadget fault tolerance bound**

Per-gadget weight bound: a single fault on a single stabilizer's
X-side gadget produces a data error of weight ≤ |gateOrdering s|.
Direct lift of `Standard.weight_bounded`. This is the building
block for multi-gadget fault tolerance reasoning. -/

/-- A single fault on the X-side gadget for stabilizer `s` produces a
    data error bounded by the stabilizer's support length. -/
theorem toCircuitStabilizerX_fault_weight_bound (spec : CodeSpec)
    (s : Fin spec.numStab) (h_pos : 0 < (spec.gateOrdering s).length)
    (fault : Fault (spec.n + 1)) :
    ErrorVec.weight (dataPauli
        (computeFaultEffect (toCircuitStabilizerX spec s) fault))
    ≤ (spec.gateOrdering s).length := by
  unfold toCircuitStabilizerX
  rw [dataPauli_weight_eq]
  exact weight_bounded spec.n (spec.gateOrdering s) fault h_pos

/-- **dataPauli equality after toCircuitX** (corollary of iter 32):
    propagating the full multi-round circuit on any initial state
    preserves the data Pauli vector as a function. This is the
    function-level lift of iter 32's pointwise `toCircuitX_data_preserved`. -/
theorem toCircuitX_dataPauli_eq (spec : CodeSpec) (es : ErrorState (spec.n + 1)) :
    dataPauli (propagateCircuit (toCircuitX spec) es) = dataPauli es := by
  funext i
  show (propagateCircuit (toCircuitX spec) es).paulis ⟨i.val, _⟩
       = es.paulis ⟨i.val, _⟩
  exact toCircuitX_data_preserved spec es i

/-- Weight of data preserved through the full circuit. -/
theorem toCircuitX_weight_eq (spec : CodeSpec) (es : ErrorState (spec.n + 1)) :
    ErrorVec.weight (dataPauli (propagateCircuit (toCircuitX spec) es))
    = ErrorVec.weight (dataPauli es) := by
  rw [toCircuitX_dataPauli_eq]

/-! ## **`computeFaultEffect` decomposition** (iter 40)

If a fault lands in the first part of a concatenated circuit
(`fault.position ≤ a.length`), then `computeFaultEffect (a ++ b) fault`
equals `propagateCircuit b (computeFaultEffect a fault)` — i.e., the
fault hits the prefix, and the suffix propagates its effect.

This is the structural fact needed to apply per-gadget weight bounds
to multi-gadget circuits. -/

/-- Decomposition: a fault in the prefix of a concatenated circuit
    is the fault on the prefix, then clean propagation of the suffix. -/
theorem computeFaultEffect_append_left {nq : Nat}
    (a b : Circuit nq) (fault : Fault nq) (h : fault.position ≤ a.length) :
    computeFaultEffect (a ++ b) fault =
    propagateCircuit b (computeFaultEffect a fault) := by
  unfold computeFaultEffect splitAt
  -- Unfold .1 / .2 of the pair
  simp only [Prod.mk]
  -- (a ++ b).take p = a.take p (since p ≤ a.length, so p - a.length = 0)
  rw [show ((a ++ b).take fault.position : Circuit nq) = a.take fault.position from by
        rw [List.take_append]
        have : fault.position - a.length = 0 := Nat.sub_eq_zero_of_le h
        simp [this]]
  -- (a ++ b).drop p = a.drop p ++ b (when p ≤ a.length)
  rw [show ((a ++ b).drop fault.position : Circuit nq) = a.drop fault.position ++ b from by
        rw [List.drop_append]
        have : fault.position - a.length = 0 := Nat.sub_eq_zero_of_le h
        simp [this]]
  -- propagateCircuit (a.drop k ++ b) es' = propagateCircuit b (propagateCircuit (a.drop k) es')
  rw [propagateCircuit_append]

end QStab.Compiler
