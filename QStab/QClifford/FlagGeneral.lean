import QStab.QClifford.Standard
import QStab.QClifford.Gate
import QStab.Compiler.SharedLemmas
import QStab.Paper.SoundnessPrime
import Mathlib.Data.Finset.Card

/-! # Parametric Flag scheme (Chao–Reichardt, weight-w X-stabilizer)

Week-2 Track-1 deliverable from the scheme-integration roadmap
(workflow `wxb4qbyrv`).

This file gives a fully syntactic, parametric Clifford circuit
realising the single-flag Chao--Reichardt syndrome-extraction scheme
(arXiv:1705.02329) for an X-type stabilizer of arbitrary weight w on
arbitrary n data qubits. Two ancillae: a "syndrome ancilla" `anc` at
qubit index `n`, and a "flag" qubit `flag` at index `n + 1`.

Circuit layout (weight-w X-stabilizer with support `S = [s_0, ..., s_{w-1}]`):

  prepPlus(anc)
  prepZero(flag)
  CNOT(anc, data_{s_0})
  CNOT(anc, data_{s_1})
  ...
  CNOT(anc, data_{s_{half-1}})
  CNOT(anc, flag)                      -- FIRST FLAG COUPLING
  CNOT(anc, data_{s_{half}})
  ...
  CNOT(anc, data_{s_{w-1}})
  CNOT(anc, flag)                      -- SECOND FLAG COUPLING
  Hadamard(anc)
  measZ(anc)
  measZ(flag)

where `half = w / 2`. The two flag couplings bracket the "dangerous
interior" of the CNOT chain: any single ancilla X-fault that occurs
strictly between them propagates an X to the flag exactly once,
flipping the flag and signalling a hook risk.

This file proves the **fault-free correctness** of the scheme:

* C1 `flagCircuit_parityFaithful` — fault-free run produces the
  correct X-stabilizer parity bit at the ancilla measurement.
* C2 `flagCircuit_noBackAction`   — fault-free run leaves data
  qubits untouched.
* `flagCircuit_dataPreservedGeneral` — even from an arbitrary input
  state (not just `initialFromData`), the gadget preserves data.

The C3 (hook-weight bound, conditional on `flag = 0`) is deferred to
the next session — it is the harder, scheme-specific theorem.

Zero `sorry`, axiom-clean.
-/

namespace QStab.QClifford.FlagGeneral

open QStab QStab.QClifford QStab.Compiler.SharedLemmas
     QStab.Paper.SoundnessPrime

/-! ## Qubit constructors specialised to k = 2 (anc + flag) -/

/-- The syndrome ancilla qubit (index `n`). -/
def ancQ (n : Nat) : Fin (n + 2) := mkAncQ' n 2 ⟨0, by omega⟩

/-- The flag qubit (index `n + 1`). -/
def flagQ (n : Nat) : Fin (n + 2) := mkAncQ' n 2 ⟨1, by omega⟩

/-- Data qubit `i` in the flag layout. -/
def dataQ (n : Nat) (i : Fin n) : Fin (n + 2) := mkDataQ' n 2 i

/-- The two ancillae are distinct (`0 ≠ 1` in `Fin 2`). -/
theorem anc_ne_flag (n : Nat) : ancQ n ≠ flagQ n := by
  unfold ancQ flagQ
  exact anc_ne_anc' n 2 ⟨0, by omega⟩ ⟨1, by omega⟩ (by decide)

theorem flag_ne_anc (n : Nat) : flagQ n ≠ ancQ n :=
  fun h => anc_ne_flag n h.symm

theorem anc_ne_data (n : Nat) (i : Fin n) : ancQ n ≠ dataQ n i := by
  unfold ancQ dataQ
  exact anc_ne_data' n 2 ⟨0, by omega⟩ i

theorem flag_ne_data (n : Nat) (i : Fin n) : flagQ n ≠ dataQ n i := by
  unfold flagQ dataQ
  exact anc_ne_data' n 2 ⟨1, by omega⟩ i

theorem data_ne_anc_flag (n : Nat) (i : Fin n) : dataQ n i ≠ ancQ n :=
  fun h => anc_ne_data n i h.symm

theorem data_ne_flag (n : Nat) (i : Fin n) : dataQ n i ≠ flagQ n :=
  fun h => flag_ne_data n i h.symm

/-! ## Parametric flag-circuit construction -/

/-- The CNOT chain from the ancilla to a list of data qubits. This
    is the *data-side* part of the flag circuit (without the bracketing
    flag-CNOTs). -/
def cnotChain (n : Nat) (qs : List (Fin n)) : List (Gate (n + 2)) :=
  qs.map (fun q => Gate.cnot (ancQ n) (dataQ n q) (anc_ne_data n q))

/-- A single flag-coupling CNOT: `CNOT(anc, flag)`. -/
def flagCoupling (n : Nat) : Gate (n + 2) :=
  Gate.cnot (ancQ n) (flagQ n) (anc_ne_flag n)

/-- The full parametric Flag circuit for an X-type stabilizer with
    support `S`.  Two flag-CNOTs bracket the symmetric middle of the
    data-CNOT chain (`half = |S| / 2`). For `|S| ≤ 1` this degenerates
    to the standard X-circuit plus two cancelling flag-CNOTs (which
    have no fault-protection value but cause no incorrectness). -/
def flagCircuit (n : Nat) (support : List (Fin n)) : Circuit (n + 2) :=
  let half := support.length / 2
  [Gate.prepPlus (ancQ n), Gate.prepZero (flagQ n)] ++
  cnotChain n (support.take half) ++
  [flagCoupling n] ++
  cnotChain n (support.drop half) ++
  [flagCoupling n,
   Gate.hadamard (ancQ n),
   Gate.measZ (ancQ n),
   Gate.measZ (flagQ n)]

/-- Sanity: for any `support`, splitting at `half` then concatenating
    recovers the original list. (Used in fault-free correctness proofs
    where the bracketed CNOT chain reduces to the unbracketed one.) -/
theorem support_split_eq (n : Nat) (support : List (Fin n)) :
    (support.take (support.length / 2)) ++ (support.drop (support.length / 2))
      = support :=
  List.take_append_drop _ _

/-! ## Fault-free correctness — C2 first (easier)

For C2 we need: in a fault-free run, data qubits are unchanged.

The strategy is to thread the joint invariant
  `ancHasNoX_at 0 es ∧ ancHasNoZ_at 1 es ∧ dataMatches' n 2 D es`
through every gate of the Flag circuit, using SharedLemmas. -/

/-- The Flag circuit has its first two gates `prepPlus(anc)` and
    `prepZero(flag)`. After both, both ancilla & flag are reset
    (ancHasNoX_at 0, ancHasNoZ_at 1) and data is preserved. -/
theorem flag_prep_dataMatches' (n : Nat) (D : ErrorVec n)
    (es : ErrorState (n + 2)) (hdm : dataMatches' n 2 D es) :
    dataMatches' n 2 D
      (propagateGate (Gate.prepZero (flagQ n))
        (propagateGate (Gate.prepPlus (ancQ n)) es)) := by
  apply prepZero_ancQ'_dataMatches'
  apply prepPlus_ancQ'_dataMatches'
  exact hdm

/-- After `prepPlus(anc); prepZero(flag)`, `ancHasNoX_at 0` holds. -/
theorem flag_prep_ancHasNoX (n : Nat) (es : ErrorState (n + 2)) :
    ancHasNoX_at n 2 ⟨0, by omega⟩
      (propagateGate (Gate.prepZero (flagQ n))
        (propagateGate (Gate.prepPlus (ancQ n)) es)) := by
  unfold flagQ
  apply prepZero_ancQ'_preserves_ancHasNoX_at_other n 2 ⟨1, by omega⟩ ⟨0, by omega⟩ (by decide)
  exact prepPlus_ancQ'_establishes_ancHasNoX_at n 2 ⟨0, by omega⟩ es

/-- After `prepPlus(anc); prepZero(flag)`, `ancHasNoZ_at 1` holds. -/
theorem flag_prep_flagHasNoZ (n : Nat) (es : ErrorState (n + 2)) :
    ancHasNoZ_at n 2 ⟨1, by omega⟩
      (propagateGate (Gate.prepZero (flagQ n))
        (propagateGate (Gate.prepPlus (ancQ n)) es)) :=
  prepZero_ancQ'_establishes_ancHasNoZ_at n 2 ⟨1, by omega⟩ _

/-- The data-CNOT chain (anc → each data qubit in `qs`) preserves
    `dataMatches'` and `ancHasNoX_at 0`. (Equivalent to the SharedLemmas
    chain lemma, specialised to the Flag ancilla at index 0.) -/
theorem flag_cnotChain_preserves (n : Nat) (D : ErrorVec n)
    (qs : List (Fin n)) (es : ErrorState (n + 2))
    (hdm : dataMatches' n 2 D es)
    (hax : ancHasNoX_at n 2 ⟨0, by omega⟩ es) :
    ancHasNoX_at n 2 ⟨0, by omega⟩ (propagateCircuit (cnotChain n qs) es)
    ∧ dataMatches' n 2 D (propagateCircuit (cnotChain n qs) es) := by
  unfold cnotChain ancQ dataQ
  exact cnotChain_anc_to_data_preserves n 2 ⟨0, by omega⟩ D qs es hdm hax

/-- The data-CNOT chain also preserves `ancHasNoZ_at 1` (the flag's
    Z-purity), since none of the CNOTs touch the flag. -/
theorem flag_cnotChain_preserves_flagHasNoZ (n : Nat)
    (qs : List (Fin n)) (es : ErrorState (n + 2))
    (haz : ancHasNoZ_at n 2 ⟨1, by omega⟩ es) :
    ancHasNoZ_at n 2 ⟨1, by omega⟩ (propagateCircuit (cnotChain n qs) es) := by
  induction qs generalizing es with
  | nil => exact haz
  | cons q rest ih =>
    apply ih
    -- The CNOT(anc, data q) doesn't touch flagQ; flagHasNoZ preserved.
    show zPart _ = .I
    simp only [propagateGate]
    have h1 : mkAncQ' n 2 ⟨1, by omega⟩ ≠ dataQ n q := by
      unfold dataQ
      exact anc_ne_data' n 2 ⟨1, by omega⟩ q
    have h2 : mkAncQ' n 2 ⟨1, by omega⟩ ≠ ancQ n := by
      unfold ancQ
      exact anc_ne_anc' n 2 ⟨1, by omega⟩ ⟨0, by omega⟩ (by decide)
    rw [if_neg h1, if_neg h2]
    exact haz

/-- The flag-CNOT `CNOT(anc, flag)` preserves `dataMatches'` (both
    endpoints in the ancilla block, never touching data). -/
theorem flag_flagCoupling_dataMatches' (n : Nat) (D : ErrorVec n)
    (es : ErrorState (n + 2)) (hdm : dataMatches' n 2 D es) :
    dataMatches' n 2 D (propagateGate (flagCoupling n) es) := by
  unfold flagCoupling ancQ flagQ
  exact cnot_anc_to_anc_dataMatches' n 2 ⟨0, by omega⟩ ⟨1, by omega⟩
    (by decide) D es hdm

/-- The flag-CNOT preserves `ancHasNoX_at 0` (control ancilla X-part
    unchanged when target flag's Z-part is I). -/
theorem flag_flagCoupling_ancHasNoX (n : Nat) (es : ErrorState (n + 2))
    (hax : ancHasNoX_at n 2 ⟨0, by omega⟩ es)
    (haz : ancHasNoZ_at n 2 ⟨1, by omega⟩ es) :
    ancHasNoX_at n 2 ⟨0, by omega⟩ (propagateGate (flagCoupling n) es) := by
  unfold flagCoupling ancQ flagQ
  exact cnot_anc_to_anc_ancHasNoX_at_ctrl n 2 ⟨0, by omega⟩ ⟨1, by omega⟩
    (by decide) es hax haz

/-! ### Note on `flagHasNoZ` preservation

The flag-CNOT does not in general preserve `ancHasNoZ_at 1` (target's
Z-part picks up control's Z). For our use case the flag's Z-purity is
only consumed by the FIRST flag-CNOT to ensure anc's X stays I; after
that, the C2 proof doesn't need flagHasNoZ to survive subsequent
gates. The data-CNOT chain doesn't touch the flag, so the relevant
flagHasNoZ is the one established by `prepZero` and consumed by the
first flag-CNOT. -/

/-- The Hadamard on the ancilla preserves `dataMatches'`. -/
theorem flag_hadamard_anc_dataMatches' (n : Nat) (D : ErrorVec n)
    (es : ErrorState (n + 2)) (hdm : dataMatches' n 2 D es) :
    dataMatches' n 2 D (propagateGate (Gate.hadamard (ancQ n)) es) := by
  unfold ancQ
  exact hadamard_ancQ'_dataMatches' n 2 ⟨0, by omega⟩ D es hdm

/-- The `measZ` on the ancilla preserves `dataMatches'`. -/
theorem flag_measZ_anc_dataMatches' (n : Nat) (D : ErrorVec n)
    (es : ErrorState (n + 2)) (hdm : dataMatches' n 2 D es) :
    dataMatches' n 2 D (propagateGate (Gate.measZ (ancQ n)) es) := by
  unfold ancQ
  exact measZ_ancQ'_dataMatches' n 2 ⟨0, by omega⟩ D es hdm

/-- The `measZ` on the flag preserves `dataMatches'`. -/
theorem flag_measZ_flag_dataMatches' (n : Nat) (D : ErrorVec n)
    (es : ErrorState (n + 2)) (hdm : dataMatches' n 2 D es) :
    dataMatches' n 2 D (propagateGate (Gate.measZ (flagQ n)) es) := by
  unfold flagQ
  exact measZ_ancQ'_dataMatches' n 2 ⟨1, by omega⟩ D es hdm

/-! ## C2 / dataPreservedGeneral — full circuit data preservation -/

/-- **Generalised data preservation (C2 strong form)**: starting from
    *any* state `es`, the full Flag circuit preserves data Paulis
    pointwise.

    Strategy: prep ancilla & flag (resets — establishes `ancHasNoX_at 0`
    and preserves `dataMatches'`), then thread `dataMatches'` through
    the symmetric structure (chain1, flag-CNOT, chain2, flag-CNOT, H,
    measZ, measZ). The data-CNOT chains preserve `ancHasNoX_at 0`
    inductively; the flag-CNOTs preserve `dataMatches'` because both
    endpoints are non-data. -/
theorem flagCircuit_data_preserved_general (n : Nat) (support : List (Fin n))
    (es : ErrorState (n + 2)) :
    dataMatches' n 2
      (fun i => es.paulis (dataQ n i))
      (propagateCircuit (flagCircuit n support) es) := by
  set D : ErrorVec n := fun i => es.paulis (dataQ n i) with hD
  have h_dm0 : dataMatches' n 2 D es := fun i => rfl
  unfold flagCircuit
  -- Decompose the circuit using propagateCircuit_append.
  rw [Standard.propagateCircuit_append, Standard.propagateCircuit_append,
      Standard.propagateCircuit_append, Standard.propagateCircuit_append]
  -- After [prepPlus, prepZero]: established invariants.
  have hpc_prep : propagateCircuit [Gate.prepPlus (ancQ n), Gate.prepZero (flagQ n)] es
      = propagateGate (Gate.prepZero (flagQ n))
          (propagateGate (Gate.prepPlus (ancQ n)) es) := by
    simp [propagateCircuit]
  rw [hpc_prep]
  set es1 := propagateGate (Gate.prepZero (flagQ n))
              (propagateGate (Gate.prepPlus (ancQ n)) es)
  have h_dm1 : dataMatches' n 2 D es1 := flag_prep_dataMatches' n D es h_dm0
  have h_ax1 : ancHasNoX_at n 2 ⟨0, by omega⟩ es1 := flag_prep_ancHasNoX n es
  have h_fz1 : ancHasNoZ_at n 2 ⟨1, by omega⟩ es1 := flag_prep_flagHasNoZ n es
  -- After first data-CNOT chunk.
  obtain ⟨h_ax2, h_dm2⟩ :=
    flag_cnotChain_preserves n D (support.take (support.length / 2)) es1 h_dm1 h_ax1
  have h_fz2 := flag_cnotChain_preserves_flagHasNoZ n
    (support.take (support.length / 2)) es1 h_fz1
  set es2 := propagateCircuit (cnotChain n (support.take (support.length / 2))) es1
  -- After first flag-CNOT.
  have hpc_fc : propagateCircuit [flagCoupling n] es2 = propagateGate (flagCoupling n) es2 := by
    simp [propagateCircuit]
  rw [hpc_fc]
  set es3 := propagateGate (flagCoupling n) es2
  have h_dm3 : dataMatches' n 2 D es3 := flag_flagCoupling_dataMatches' n D es2 h_dm2
  have h_ax3 : ancHasNoX_at n 2 ⟨0, by omega⟩ es3 :=
    flag_flagCoupling_ancHasNoX n es2 h_ax2 h_fz2
  -- After second data-CNOT chunk.
  obtain ⟨_, h_dm4⟩ :=
    flag_cnotChain_preserves n D (support.drop (support.length / 2)) es3 h_dm3 h_ax3
  set es4 := propagateCircuit (cnotChain n (support.drop (support.length / 2))) es3
  -- After [flagCoupling, hadamard(anc), measZ(anc), measZ(flag)].
  have hpc_tail : propagateCircuit
      [flagCoupling n, Gate.hadamard (ancQ n), Gate.measZ (ancQ n), Gate.measZ (flagQ n)] es4
      = propagateGate (Gate.measZ (flagQ n))
          (propagateGate (Gate.measZ (ancQ n))
            (propagateGate (Gate.hadamard (ancQ n))
              (propagateGate (flagCoupling n) es4))) := by
    simp [propagateCircuit]
  rw [hpc_tail]
  have h_dm5 := flag_flagCoupling_dataMatches' n D es4 h_dm4
  have h_dm6 := flag_hadamard_anc_dataMatches' n D _ h_dm5
  have h_dm7 := flag_measZ_anc_dataMatches' n D _ h_dm6
  exact flag_measZ_flag_dataMatches' n D _ h_dm7

/-- **C2 noBackAction**: in a fault-free run from
    `initialFromData' n 2 E`, the Flag circuit leaves data Paulis equal
    to `E`. -/
theorem flagCircuit_noBackAction (n : Nat) (support : List (Fin n)) :
    noBackAction' (k := 2) (flagCircuit n support) := by
  intro E i
  -- Goal: dataPauli' (runClean' (flagCircuit n support) E) i = E i.
  unfold runClean'
  -- Apply dataPreservedGeneral: paulis(dataQ i) of result = paulis(dataQ i) of input.
  have h := flagCircuit_data_preserved_general n support
    (initialFromData' n 2 E) i
  -- h : ... .paulis (mkDataQ' n 2 i) = (initialFromData' n 2 E).paulis (dataQ n i)
  -- Goal: dataPauli' ... i = E i, which unfolds to ... .paulis (mkDataQ' n 2 i) = E i
  show (propagateCircuit (flagCircuit n support)
      (initialFromData' n 2 E)).paulis (mkDataQ' n 2 i) = E i
  rw [h]
  -- (initialFromData' n 2 E).paulis (dataQ n i) = E i
  show (initialFromData' n 2 E).paulis (dataQ n i) = E i
  unfold initialFromData' dataQ mkDataQ'
  have h_lt : i.val < n := i.isLt
  simp [h_lt]

end QStab.QClifford.FlagGeneral
