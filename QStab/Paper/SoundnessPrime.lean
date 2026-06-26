import QStab.Paper.Bridge
import QStab.Paper.Soundness
import QStab.QClifford.Standard
import QStab.PauliOps

/-!
# Refined QStab soundness predicates for multi-ancilla schemes

This file is the Layer-1 design from the scheme-references workflow
`wxb4qbyrv` (2026-06-13). It introduces a *parametric-arity* version
of `SchemeCorrect` so that schemes with more than one ancilla per
gadget (Shor cat ancillae + verifier; Chao--Reichardt flag ancilla;
Knill block teleportation) can be expressed in the same Lean framework
as the standard single-ancilla CNOT scheme.

Three changes relative to `Paper/Soundness.lean`:

1. **Variable arity**: gadgets now live in `Circuit (n + k)` where `k`
   is the per-gadget ancilla count (`k = 1` recovers the standard
   scheme).
2. **Scheme-supplied syndrome reader**: instead of fixing
   `measFlipped n es := es.measFlips ⟨n, _⟩`, each scheme supplies
   its own `syndromeBit : ErrorState (n+k) → Bool` — Shor XORs across
   the cat block, flag schemes ignore the flag bit when reading the
   syndrome, etc.
3. **Conditional hook bound with stabilizer-coset disjunct**:
   `boundedHook'` now reads "weight ≥ 2 ∧ goodClassical = true →
   weight ≤ r ∨ trueWeight T_s dataPauli ≤ r". The `goodClassical`
   predicate captures verifier=0 / flag=0 / always-true; the second
   disjunct absorbs the "anc-X before any data CNOT propagates the
   full stabilizer" case that arises for Flag and Shor, AND its
   weaker stabilizer-coset analogue (e.g. the length-4 Flag
   sub-case where the residual is `[I, X, X, X]` ≡_S `[X, I, I, I]`
   of true weight 1).

The unprimed `Soundness.SchemeCorrect` is preserved verbatim. A
forward adapter `SchemeCorrect_lift_to_prime` will be added in
`Compiler/StandardIntoBundlePrime.lean` to ensure the existing
standard pipeline continues to compile without modification.

This file contains zero `sorry` and no custom axioms.
-/

namespace QStab.Paper.SoundnessPrime

open QStab QStab.QClifford QStab.Paper QStab.Paper.Soundness

/-! ## Variable-arity helpers -/

/-- Data Pauli projection (multi-ancilla version). The first `n`
    qubits of an `ErrorState (n + k)` are the data; qubits
    `n..n+k-1` are scheme-specific ancillae (syndrome ancilla,
    flag, verifier, cat block — the scheme decides). -/
def dataPauli' {n k : Nat} (es : ErrorState (n + k)) : ErrorVec n :=
  fun i => es.paulis ⟨i.val, by have := i.isLt; omega⟩

/-- Data error weight in the multi-ancilla setting. Equals
    `ErrorVec.weight (dataPauli' es)`. -/
def dataWt' {n k : Nat} (es : ErrorState (n + k)) : Nat :=
  ErrorVec.weight (dataPauli' (k := k) es)

theorem dataPauli'_weight_eq {n k : Nat} (es : ErrorState (n + k)) :
    ErrorVec.weight (dataPauli' (k := k) es) = dataWt' (k := k) es := rfl

/-- Initial state lifting a data Pauli vector into a multi-ancilla
    `ErrorState`: data qubits carry `E`, every ancilla index
    `n..n+k-1` carries `I`, no measurement flips. -/
def initialFromData' (n k : Nat) (E : ErrorVec n) : ErrorState (n + k) where
  paulis := fun i => if h : i.val < n then E ⟨i.val, h⟩ else .I
  measFlips := fun _ => false

/-- Fault-free run of a multi-ancilla gadget on input data `E`. -/
def runClean' {n k : Nat} (Γ : Circuit (n + k)) (E : ErrorVec n) :
    ErrorState (n + k) :=
  propagateCircuit Γ (initialFromData' n k E)

/-! ## Refined correctness predicates -/

/-- **(C1')** Parity-faithfulness with a scheme-supplied syndrome
    reader.  The standard scheme instantiates `syndromeBit` with
    `fun es => es.measFlips ⟨n, _⟩`; Shor instantiates it with the
    XOR of the cat-block ancilla flips; flag schemes ignore the
    flag bit when reading the syndrome. -/
def parityFaithful' {n k : Nat} (Γ : Circuit (n + k)) (T_s : ErrorVec n)
    (syndromeBit : ErrorState (n + k) → Bool) : Prop :=
  ∀ (E : ErrorVec n), syndromeBit (runClean' Γ E) = ErrorVec.parity T_s E

/-- **(C2')** No data back-action — a fault-free run preserves the
    data Pauli vector pointwise, irrespective of how many ancillae
    the gadget uses. -/
def noBackAction' {n k : Nat} (Γ : Circuit (n + k)) : Prop :=
  ∀ (E : ErrorVec n) (i : Fin n),
    dataPauli' (k := k) (runClean' Γ E) i = E i

/-! ## Stabilizer-modular true weight

Two data Paulis `E` and `E · T_s` are *logically equivalent* (act
identically on the codespace), so the "true" weight of a residual
error is the minimum over its stabilizer-coset.

`trueWeight` is the *mathematically correct* notion of residual
weight on the codespace, and it is the second disjunct used by
`boundedHook'` below.  Earlier (pre-2026-06-14) iterations of
`boundedHook'` used the stricter disjunct `dataPauli = T_s`, but
that form is too rigid for length-4 (and higher) Flag schemes
where a single fault can produce a residual like `[I, X, X, X]`
on a length-4 stabilizer `[X, X, X, X]`: the residual is NOT
literally equal to `T_s`, yet it is stabilizer-equivalent to a
weight-1 error `[X, I, I, I]`, hence logically correctable.  The
`trueWeight` disjunct admits exactly this case.

`weight ≤ r` implies `trueWeight ≤ r` via `trueWeight_le_weight`,
and `dataPauli = T_s` implies `trueWeight ≤ r` (for any r ≥ 0)
via `trueWeight_le_of_weight_or_stab`.  So the new `boundedHook'`
is strictly weaker than (i.e., implied by) the historical one. -/

/-- Multiply `E` pointwise by `T_s` (the X-type stabilizer pauli
    vector). `(mulByStab T_s E) i = pauliMul (T_s i) (E i)`. -/
def mulByStab {n : Nat} (T_s : ErrorVec n) (E : ErrorVec n) : ErrorVec n :=
  fun i => pauliMul (T_s i) (E i)

/-- The *true* logical weight of a data Pauli vector `E` for the
    stabilizer `T_s`: the minimum of `weight E` and `weight (E · T_s)`. -/
def trueWeight {n : Nat} (T_s : ErrorVec n) (E : ErrorVec n) : Nat :=
  min (ErrorVec.weight E) (ErrorVec.weight (mulByStab T_s E))

/-- `trueWeight ≤ weight` (mod stab can only decrease the weight). -/
theorem trueWeight_le_weight {n : Nat} (T_s E : ErrorVec n) :
    trueWeight T_s E ≤ ErrorVec.weight E :=
  Nat.min_le_left _ _

/-- The raw `weight ≤ r ∨ dataPauli = T_s` disjunct (the historical
    `boundedHook'` form) *implies* `trueWeight ≤ r` (mod stab).
    Used to bridge raw-form proofs into the modularised view. -/
theorem trueWeight_le_of_weight_or_stab {n : Nat} (T_s E : ErrorVec n)
    (r : Nat) (h : ErrorVec.weight E ≤ r ∨ E = T_s) :
    trueWeight T_s E ≤ r := by
  rcases h with hw | hE
  · exact Nat.le_trans (trueWeight_le_weight T_s E) hw
  · -- E = T_s ⇒ mulByStab T_s E = fun i => I, weight = 0 ≤ r.
    have hms : mulByStab T_s E = fun _ => Pauli.I := by
      funext i
      simp [mulByStab, hE]
    have hw0 : ErrorVec.weight (mulByStab T_s E) = 0 := by
      rw [hms]
      simp [ErrorVec.weight]
    have : trueWeight T_s E ≤ ErrorVec.weight (mulByStab T_s E) :=
      Nat.min_le_right _ _
    omega

/-- **(C3')** Conditional, stabilizer-coset-tolerant hook bound.

    "If the residual data weight is ≥ 2 (Type-II hook) AND the
    classical accept-condition `goodClassical` holds (verifier = 0,
    flag = 0, or always for the standard scheme), then either the
    raw weight is ≤ r, OR the *true* (stabilizer-coset) weight of
    the residual is ≤ r — equivalently the residual is logically
    equivalent to some weight-≤-r error on the codespace."

    The standard CNOT scheme instantiates `goodClassical := fun _ ↦
    true` and the second disjunct is never witnessed (the standard
    scheme has no stabilizer-overlap hook). Flag schemes have
    `goodClassical := ¬ flagFlipped` and witness the disjunct on
    the length-4 anc-X-early sub-case (`[I, X, X, X]` ≡_S
    `[X, I, I, I]`, true weight 1).  Shor has `goodClassical := ¬
    verifierFlipped` and witnesses the disjunct on cascade-X
    faults that flip the verifier symmetrically. -/
def boundedHook' {n k : Nat} (Γ : Circuit (n + k)) (T_s : ErrorVec n)
    (r : Nat) (goodClassical : ErrorState (n + k) → Bool) : Prop :=
  ∀ (fault : Fault (n + k)),
    ErrorVec.weight (dataPauli' (k := k) (computeFaultEffect Γ fault)) ≥ 2 →
    goodClassical (computeFaultEffect Γ fault) = true →
    ErrorVec.weight (dataPauli' (k := k) (computeFaultEffect Γ fault)) ≤ r ∨
    trueWeight T_s
      (dataPauli' (k := k) (computeFaultEffect Γ fault)) ≤ r

/-- A scheme is **correct'** for measuring `T_s` with back-action
    weight bound `r`, syndrome reader `syndromeBit`, and classical
    accept-condition `goodClassical`, if it satisfies C1' + C2' +
    C3'. -/
def SchemeCorrect' {n k : Nat} (Γ : Circuit (n + k)) (T_s : ErrorVec n)
    (r : Nat) (syndromeBit : ErrorState (n + k) → Bool)
    (goodClassical : ErrorState (n + k) → Bool) : Prop :=
  parityFaithful' Γ T_s syndromeBit ∧ noBackAction' Γ ∧
    boundedHook' Γ T_s r goodClassical

/-! ## Trivial-condition instance: standard schemes (`k=1`)

    For the standard CNOT scheme there is exactly one ancilla
    (`k = 1`), `syndromeBit` reads that ancilla's `measFlips`, and
    `goodClassical` is the constant-true predicate. The refined
    `SchemeCorrect'` then collapses to the original `SchemeCorrect`
    up to the stabilizer-overlap disjunct (which is always
    discharged on the weight branch for the standard scheme).

    Helpers below are used by the adapter
    `Compiler/StandardIntoBundlePrime.lean` to lift existing
    standard-scheme proofs into the new framework without
    reproving anything. -/

/-- The constant-true classical predicate. -/
@[reducible] def alwaysGood {n k : Nat} :
    ErrorState (n + k) → Bool := fun _ => true

/-- Standard single-ancilla syndrome reader: the lone ancilla sits
    at index `n` of `ErrorState (n + 1)`. -/
def standardSyndromeBit (n : Nat) (es : ErrorState (n + 1)) : Bool :=
  es.measFlips ⟨n, by omega⟩

/-! ## Definitional bridges to the existing single-ancilla layer

These bridges document that the primed predicates are
definitionally equal to the unprimed ones for `k = 1`, so the
standard-scheme proofs in `Compiler/SchemeCorrectStandard.lean`
lift to the new framework via `rfl`-style rewrites in
`StandardIntoBundlePrime.lean`. -/

theorem dataPauli'_eq_dataPauli (n : Nat) (es : ErrorState (n + 1)) :
    dataPauli' (k := 1) es = Soundness.dataPauli es := by
  funext i
  unfold dataPauli' Soundness.dataPauli QStab.QClifford.Standard.dataErr
  rfl

theorem initialFromData'_eq_initialFromData (n : Nat) (E : ErrorVec n) :
    initialFromData' n 1 E = Soundness.initialFromData E := by
  unfold initialFromData' Soundness.initialFromData
  rfl

theorem runClean'_eq_runClean (n : Nat) (Γ : Circuit (n + 1))
    (E : ErrorVec n) :
    runClean' (k := 1) Γ E = Soundness.runClean Γ E := by
  unfold runClean' Soundness.runClean
  rw [initialFromData'_eq_initialFromData]

theorem standardSyndromeBit_eq_measFlipped (n : Nat) (es : ErrorState (n + 1)) :
    standardSyndromeBit n es =
      QStab.QClifford.Standard.measFlipped n es := by
  unfold standardSyndromeBit QStab.QClifford.Standard.measFlipped
  rfl

/-! ## Standard-scheme lift to the prime predicates

Given a proof of the original `SchemeCorrect` from
`Soundness.lean`, the lifted statement (with `k = 1`,
`syndromeBit = standardSyndromeBit`, `goodClassical = alwaysGood`)
reduces to the same content modulo the stabilizer-overlap
disjunct, which is always discharged via the weight branch (the
standard scheme has no full-stabilizer hook). -/

theorem schemeCorrect_lift {n : Nat} (Γ : Circuit (n + 1))
    (T_s : ErrorVec n) (r : Nat)
    (h : Soundness.SchemeCorrect Γ T_s r) :
    SchemeCorrect' (k := 1) Γ T_s r (standardSyndromeBit n)
      (alwaysGood (k := 1)) := by
  obtain ⟨hC1, hC2, hC3⟩ := h
  refine ⟨?c1, ?c2, ?c3⟩
  · -- C1' parityFaithful'
    intro E
    rw [standardSyndromeBit_eq_measFlipped, runClean'_eq_runClean]
    exact hC1 E
  · -- C2' noBackAction'
    intro E i
    rw [dataPauli'_eq_dataPauli, runClean'_eq_runClean]
    exact hC2 E i
  · -- C3' boundedHook' — discharge via weight branch (stabilizer
    -- disjunct never invoked for the standard scheme).
    intro fault hwt _
    rw [dataPauli'_eq_dataPauli] at hwt ⊢
    refine Or.inl ?_
    have := hC3 fault
    rw [Soundness.dataPauli_weight_eq] at this
    rw [Soundness.dataPauli_weight_eq]
    exact this hwt

end QStab.Paper.SoundnessPrime
