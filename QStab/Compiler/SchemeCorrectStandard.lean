import QStab.QClifford.Standard
import QStab.Paper.Soundness

/-! # `SchemeCorrect` for the standard CNOT scheme

Phase B (session 2, iter 9-10). Discharges the `SchemeCorrect`
hypothesis that `qstab_sound` requires.

`SchemeCorrect Γ T_s r := parityFaithful Γ T_s ∧ noBackAction Γ ∧
boundedHook Γ r` where:
- **C2 (noBackAction)**: `dataPauli (runClean Γ E) i = E i`.
  *This file (iter 10): full assembly for xCircuit.*
- **C1 (parityFaithful)**: `measFlipped (runClean Γ E) = parity T_s E`.
  *Iter 11 task.*
- **C3 (boundedHook)**: already proven by `Standard.weight_bounded`.
-/

namespace QStab.Compiler.SchemeCorrectStandard

open QStab QStab.QClifford QStab.QClifford.Standard QStab.Paper.Soundness ErrorVec

/-! ## `dataMatches`: each data qubit equals an externally fixed input -/

/-- `dataMatches E es`: each data qubit of `es` (indices `0..n-1`)
    carries Pauli `E i`. -/
def dataMatches {n : Nat} (E : ErrorVec n) (es : ErrorState (n + 1)) : Prop :=
  ∀ i : Fin n, es.paulis (mkDataQubit n i) = E i

/-- The clean state with `E` injected satisfies `dataMatches E`. -/
theorem dataMatches_init {n : Nat} (E : ErrorVec n) :
    dataMatches E (initialFromData E) := by
  intro i
  simp only [initialFromData, mkDataQubit]
  have h_lt : i.val < n := i.isLt
  simp [h_lt]

/-- `prepPlus` on the ancilla preserves `dataMatches`. -/
theorem dataMatches_prepPlus_anc {n : Nat} (E : ErrorVec n)
    (es : ErrorState (n+1)) (h : dataMatches E es) :
    dataMatches E (propagateGate (Gate.prepPlus (ancQubit n)) es) := by
  intro i
  simp only [propagateGate]
  rw [if_neg (Ne.symm (anc_ne_data n i))]
  exact h i

/-- `Hadamard` on the ancilla preserves `dataMatches`. -/
theorem dataMatches_hadamard_anc {n : Nat} (E : ErrorVec n)
    (es : ErrorState (n+1)) (h : dataMatches E es) :
    dataMatches E (propagateGate (Gate.hadamard (ancQubit n)) es) := by
  intro i
  simp only [propagateGate]
  rw [if_neg (Ne.symm (anc_ne_data n i))]
  exact h i

/-- `measZ` on the ancilla preserves `dataMatches`. -/
theorem dataMatches_measZ_anc {n : Nat} (E : ErrorVec n)
    (es : ErrorState (n+1)) (h : dataMatches E es) :
    dataMatches E (propagateGate (Gate.measZ (ancQubit n)) es) := by
  intro i
  simp only [propagateGate]
  exact h i

/-- `CNOT(anc, q)` preserves `dataMatches` if the ancilla has no
    X-component. The proof: at target `q`, the contribution from
    control is `xPart anc = I`, so the target is unchanged
    (`pauliMul I E = E`); other data qubits are untouched. -/
theorem dataMatches_cnot_anc_to_data {n : Nat} (E : ErrorVec n)
    (q : Fin n) (es : ErrorState (n+1))
    (h : dataMatches E es) (hax : ancHasNoX n es) :
    dataMatches E (propagateGate
      (Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) es) := by
  intro i
  simp only [propagateGate]
  by_cases hiq : i = q
  · -- i = q: target qubit. X-from-control is I, so pauliMul I (es.paulis t) = es.paulis t.
    subst hiq
    rw [if_pos rfl]
    have hax' : xPart (es.paulis (ancQubit n)) = .I := hax
    rw [hax']
    show pauliMul Pauli.I _ = E i
    rw [pauliMul_I_left]
    exact h i
  · -- i ≠ q: not the target. Also i is a data index, not the ancilla.
    have h1 : mkDataQubit n i ≠ mkDataQubit n q := by
      simp [mkDataQubit, Fin.ext_iff]
      intro h'; exact hiq (Fin.ext h')
    have h2 : mkDataQubit n i ≠ ancQubit n := data_ne_anc n i
    rw [if_neg h1, if_neg h2]
    exact h i

/-! ## Assembly: induct over the CNOT support list -/

/-- Induction: the CNOT-chain (anc → each data qubit in `qs`) preserves
    both `ancHasNoX` and `dataMatches E`. -/
theorem ancHasNoX_dataMatches_cnotChain {n : Nat} (E : ErrorVec n)
    (qs : List (Fin n)) (es : ErrorState (n+1))
    (hax : ancHasNoX n es) (hdm : dataMatches E es) :
    ancHasNoX n (propagateCircuit
      (qs.map fun q => Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) es)
    ∧ dataMatches E (propagateCircuit
      (qs.map fun q => Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) es) := by
  induction qs generalizing es with
  | nil => exact ⟨hax, hdm⟩
  | cons q rest ih =>
    simp only [List.map, propagateCircuit]
    obtain ⟨hax', _⟩ := cnot_anc_ancNoX n q es hax
    have hdm' : dataMatches E (propagateGate _ es) :=
      dataMatches_cnot_anc_to_data E q es hdm hax
    exact ih _ hax' hdm'

/-- `prepPlus` on the ancilla yields `ancHasNoX` regardless of input. -/
theorem ancHasNoX_prepPlus_anc {n : Nat} (es : ErrorState (n+1)) :
    ancHasNoX n (propagateGate (Gate.prepPlus (ancQubit n)) es) := by
  show xPart _ = .I
  simp [propagateGate, xPart]

/-- The initial state with E injected has `ancHasNoX` (ancilla = I). -/
theorem ancHasNoX_initialFromData {n : Nat} (E : ErrorVec n) :
    ancHasNoX n (initialFromData E) := by
  show xPart _ = .I
  simp [initialFromData, ancQubit, xPart]

/-- The bedrock dataMatches lemma: full xCircuit preserves data
    qubits. -/
theorem xCircuit_dataMatches_preserved {n : Nat} (support : List (Fin n))
    (E : ErrorVec n) :
    dataMatches E (propagateCircuit (xCircuit n support) (initialFromData E)) := by
  unfold xCircuit
  rw [propagateCircuit_append, propagateCircuit_append]
  -- After prepPlus block: ancHasNoX + dataMatches preserved (dataMatches via prepPlus, ancHasNoX strengthens)
  set es0 := initialFromData E
  -- propagateCircuit [prepPlus] es0 = propagateGate prepPlus es0
  have hpc1 : propagateCircuit [Gate.prepPlus (ancQubit n)] es0 =
              propagateGate (Gate.prepPlus (ancQubit n)) es0 := by
    simp [propagateCircuit]
  rw [hpc1]
  set es1 := propagateGate (Gate.prepPlus (ancQubit n)) es0
  have h_ax1 : ancHasNoX n es1 := ancHasNoX_prepPlus_anc es0
  have h_dm1 : dataMatches E es1 :=
    dataMatches_prepPlus_anc E es0 (dataMatches_init E)
  -- After CNOT chain: dataMatches preserved (ancHasNoX also preserved but not needed downstream)
  obtain ⟨_, h_dm2⟩ := ancHasNoX_dataMatches_cnotChain E support es1 h_ax1 h_dm1
  set es2 := propagateCircuit (support.map _) es1
  -- After [hadamard, measZ]: dataMatches preserved (neither gate touches data).
  simp only [propagateCircuit]
  have h_dm3 := dataMatches_hadamard_anc E es2 h_dm2
  exact dataMatches_measZ_anc E _ h_dm3

/-- **C2 noBackAction for `xCircuit`**: the standard X-side gadget
    leaves data qubits unchanged on a fault-free run. -/
theorem xCircuit_noBackAction {n : Nat} (support : List (Fin n)) :
    noBackAction (xCircuit n support) := by
  intro E i
  show dataErr n (propagateCircuit (xCircuit n support) (initialFromData E)) i = E i
  simp only [dataErr]
  exact xCircuit_dataMatches_preserved support E i

/-! ## Towards C1 (parityFaithful) — ancilla Pauli accumulation

For C1, we need to track what Pauli the ancilla carries after the
CNOT chain. Initial ancilla = I (after prepPlus). Each CNOT(anc, q)
accumulates `pauliMul (zPart (E q)) (anc.paulis)` onto the ancilla,
because the Z-component of the target qubit propagates back to the
control. After the chain, anc.paulis is a product of `zPart` values
over support qubits.

After Hadamard: paulis swap X↔Z; after measZ: hasXComp flips
measFlips. So the measurement-flip parity equals the parity of
Z-components of `E` over `support`. -/

/-- After `CNOT(anc, q)`: if the ancilla had no X-component, the new
    ancilla Pauli is `pauliMul (zPart (es.paulis q-data)) (es.paulis anc)`.
    Data qubits are unchanged (when ancNoX holds — see
    `dataMatches_cnot_anc_to_data`). -/
theorem cnot_anc_to_data_anc_paulis {n : Nat} (q : Fin n)
    (es : ErrorState (n+1)) (_hax : ancHasNoX n es) :
    (propagateGate (Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) es).paulis
      (ancQubit n)
    = pauliMul (zPart (es.paulis (mkDataQubit n q))) (es.paulis (ancQubit n)) := by
  simp only [propagateGate]
  have h_ne : ancQubit n ≠ mkDataQubit n q := anc_ne_data n q
  rw [if_neg h_ne]
  simp

/-- Symbolic accumulation of zPart contributions across a list of
    support qubits. Inner CNOTs in the chain multiply the ancilla by
    `zPart (E q)` for each `q ∈ qs`. We use `foldr` (right-fold): for
    `qs = [q₀, q₁, q₂]`, the result is
    `pauliMul (zPart (E q₀)) (pauliMul (zPart (E q₁)) (pauliMul (zPart (E q₂)) I))`.
    Since `zPart` values are in `{I, Z}` and these commute, the
    associativity order doesn't matter. -/
def productZPart {n : Nat} (qs : List (Fin n)) (E : ErrorVec n) : Pauli :=
  qs.foldr (fun q acc => pauliMul (zPart (E q)) acc) Pauli.I

@[simp] theorem productZPart_nil {n : Nat} (E : ErrorVec n) :
    productZPart ([] : List (Fin n)) E = Pauli.I := rfl

@[simp] theorem productZPart_cons {n : Nat} (q : Fin n) (qs : List (Fin n))
    (E : ErrorVec n) :
    productZPart (q :: qs) E = pauliMul (zPart (E q)) (productZPart qs E) := rfl

/-! ### Auxiliary: pauliMul commutativity on the `{I, Z}` × `{I, Z}` subgroup -/

private theorem pauliMul_zPart_zPart_assoc (p q r : Pauli) :
    pauliMul (zPart p) (pauliMul (zPart q) r) =
    pauliMul (zPart q) (pauliMul (zPart p) r) := by
  cases p <;> cases q <;> cases r <;>
    simp [zPart, pauliMul]

/-- **Key C1 step**: after propagating the CNOT chain from an
    ancHasNoX + dataMatches state, the ancilla Pauli equals the
    `productZPart` accumulator multiplied with the initial ancilla
    Pauli. Body: induction on `qs`, using `cnot_anc_to_data_anc_paulis`
    and the inductive `ancHasNoX_dataMatches_cnotChain` to maintain
    both invariants. -/
theorem cnotChain_anc_paulis {n : Nat} (qs : List (Fin n)) (E : ErrorVec n)
    (es : ErrorState (n+1)) (hdm : dataMatches E es) (hax : ancHasNoX n es) :
    (propagateCircuit
      (qs.map fun q => Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) es).paulis
      (ancQubit n)
    = pauliMul (productZPart qs E) (es.paulis (ancQubit n)) := by
  induction qs generalizing es with
  | nil =>
    simp [productZPart, propagateCircuit]
  | cons q rest ih =>
    simp only [List.map, propagateCircuit, productZPart_cons]
    -- Step 1: After CNOT(anc, q), anc.paulis = pauliMul (zPart (es.paulis (data q))) (es.paulis anc).
    --         By dataMatches, es.paulis (data q) = E q.
    set es1 := propagateGate (Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) es
    have h_es1_anc : es1.paulis (ancQubit n) =
        pauliMul (zPart (E q)) (es.paulis (ancQubit n)) := by
      have := cnot_anc_to_data_anc_paulis q es hax
      rw [this]
      congr 1
      exact congrArg zPart (hdm q)
    -- Step 2: After the chain on rest, by IH (with updated dataMatches and ancHasNoX).
    have hax1 : ancHasNoX n es1 := (cnot_anc_ancNoX n q es hax).1
    have hdm1 : dataMatches E es1 := dataMatches_cnot_anc_to_data E q es hdm hax
    have ih1 := ih es1 hdm1 hax1
    rw [ih1, h_es1_anc]
    -- Goal:
    --   pauliMul (productZPart rest E) (pauliMul (zPart (E q)) (es.paulis anc))
    -- = pauliMul (pauliMul (zPart (E q)) (productZPart rest E)) (es.paulis anc)
    -- These should be equal via associativity + commutativity over {I, Z}.
    -- Reduce by induction on rest: productZPart rest E is built from zParts, so commutes with zPart (E q).
    clear ih ih1
    induction rest with
    | nil =>
      simp [productZPart]
    | cons q' rest' ih' =>
      simp only [productZPart_cons]
      -- LHS: pauliMul (pauliMul (zPart (E q')) (productZPart rest' E))
      --                (pauliMul (zPart (E q)) (es.paulis (ancQubit n)))
      -- RHS: pauliMul (pauliMul (zPart (E q))
      --                (pauliMul (zPart (E q')) (productZPart rest' E)))
      --                (es.paulis (ancQubit n))
      -- Strategy: case-split on the relevant Paulis. Brute force.
      set A := es.paulis (ancQubit n)
      set PX := productZPart rest' E
      cases hq : zPart (E q) <;> cases hq' : zPart (E q') <;>
        cases hx : PX <;> cases hA : A <;> simp_all [pauliMul]

/-! ## Canonical X-stabilizer over a support, and the
    anc-after-prepPlus-then-CNOTchain identity -/

/-- The canonical X-stabilizer indexed by `support`: `Pauli.X` on
    qubits in `support`, `Pauli.I` elsewhere. This is the `T_s` for
    which `xCircuit n support` is the parity-measurement gadget. -/
def Xstabilizer {n : Nat} (support : List (Fin n)) : ErrorVec n :=
  fun i => if i ∈ support then Pauli.X else Pauli.I

/-- After `prepPlus(anc)` from `initialFromData E`, the ancilla Pauli
    is `Pauli.I` (the prepPlus reset). -/
theorem prepPlus_anc_paulis {n : Nat} (E : ErrorVec n) :
    (propagateGate (Gate.prepPlus (ancQubit n)) (initialFromData E)).paulis
      (ancQubit n) = Pauli.I := by
  simp [propagateGate]

/-- **C1 step 2**: after `prepPlus + CNOT chain`, the ancilla Pauli
    equals `productZPart support E` (with `pauliMul I` already
    simplified). -/
theorem prep_cnotChain_anc_paulis {n : Nat} (support : List (Fin n))
    (E : ErrorVec n) :
    (propagateCircuit
      ((support.map fun q =>
          Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)))
      (propagateGate (Gate.prepPlus (ancQubit n)) (initialFromData E))).paulis
      (ancQubit n) = productZPart support E := by
  set es1 := propagateGate (Gate.prepPlus (ancQubit n)) (initialFromData E)
  have h_ax : ancHasNoX n es1 := ancHasNoX_prepPlus_anc (initialFromData E)
  have h_dm : dataMatches E es1 :=
    dataMatches_prepPlus_anc E (initialFromData E) (dataMatches_init E)
  have h_chain := cnotChain_anc_paulis support E es1 h_dm h_ax
  rw [h_chain]
  -- anc.paulis of es1 = I (from prepPlus_anc_paulis)
  rw [prepPlus_anc_paulis]
  -- pauliMul (productZPart support E) Pauli.I = productZPart support E
  cases h : productZPart support E <;> simp [pauliMul]

/-! ## Hadamard + measZ: measFlipped formula -/

/-- `zPart` always returns `I` or `Z`. -/
private theorem zPart_in_IZ (p : Pauli) : zPart p = Pauli.I ∨ zPart p = Pauli.Z := by
  cases p <;> simp [zPart]

/-- `productZPart support E` is always in `{I, Z}` (built from `zPart`
    values via `pauliMul`). -/
theorem productZPart_in_IZ {n : Nat} (qs : List (Fin n)) (E : ErrorVec n) :
    productZPart qs E = Pauli.I ∨ productZPart qs E = Pauli.Z := by
  induction qs with
  | nil => left; rfl
  | cons q rest ih =>
    simp only [productZPart_cons]
    rcases ih with hI | hZ
    · rw [hI]
      rcases zPart_in_IZ (E q) with h | h
      · rw [h]; left; rfl
      · rw [h]; right; rfl
    · rw [hZ]
      rcases zPart_in_IZ (E q) with h | h
      · rw [h]; right; rfl
      · rw [h]; left; rfl

/-- prepPlus, CNOT, and hadamard all preserve the `measFlips` field
    (only `measZ` modifies measFlips). -/
private theorem prepPlus_preserves_measFlips {n : Nat} (q : Fin (n+1))
    (es : ErrorState (n+1)) :
    (propagateGate (Gate.prepPlus q) es).measFlips = es.measFlips := by
  simp [propagateGate]

private theorem cnot_preserves_measFlips {n : Nat} (c t : Fin (n+1)) (hne : c ≠ t)
    (es : ErrorState (n+1)) :
    (propagateGate (Gate.cnot c t hne) es).measFlips = es.measFlips := by
  simp [propagateGate]

private theorem hadamard_preserves_measFlips {n : Nat} (q : Fin (n+1))
    (es : ErrorState (n+1)) :
    (propagateGate (Gate.hadamard q) es).measFlips = es.measFlips := by
  simp [propagateGate]

/-- After the CNOT chain, none of the gates have touched the
    ancilla's measFlips bit yet (none of prepPlus, CNOT, hadamard
    write to measFlips). So measFlips at anc is still `false`. -/
theorem prep_cnotChain_hadamard_measFlips {n : Nat} (support : List (Fin n))
    (E : ErrorVec n) :
    (propagateCircuit
      ([Gate.prepPlus (ancQubit n)] ++
        (support.map fun q =>
          Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) ++
        [Gate.hadamard (ancQubit n)]) (initialFromData E)).measFlips
      (ancQubit n) = false := by
  rw [propagateCircuit_append, propagateCircuit_append]
  -- After prepPlus: measFlips unchanged.
  simp only [propagateCircuit, hadamard_preserves_measFlips]
  -- After CNOT chain: measFlips unchanged.
  suffices h : ∀ (qs : List (Fin n)) (es : ErrorState (n+1)),
      (propagateCircuit (qs.map fun q =>
        Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) es).measFlips =
      es.measFlips by
    rw [h]
    simp [propagateGate, initialFromData]
  intro qs
  induction qs with
  | nil => intro _; simp [propagateCircuit]
  | cons q rest ih =>
    intro es
    simp only [List.map, propagateCircuit]
    rw [ih]
    exact cnot_preserves_measFlips _ _ _ es

/-- **C1 ancilla measFlipped equation**: after the full `xCircuit n
    support`, `measFlipped` at the ancilla equals
    `hasXComp (hadamardAction (productZPart support E))`. -/
theorem xCircuit_measFlipped_eq_hasXComp {n : Nat} (support : List (Fin n))
    (E : ErrorVec n) :
    measFlipped n (propagateCircuit (xCircuit n support) (initialFromData E))
    = hasXComp (hadamardAction (productZPart support E)) := by
  unfold xCircuit measFlipped
  -- xCircuit = prepPlus ++ cnots ++ [hadamard, measZ] =
  --           ([prepPlus] ++ cnots ++ [hadamard]) ++ [measZ]
  rw [show ([Gate.prepPlus (ancQubit n)] ++
            (support.map fun q =>
              Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) ++
            [Gate.hadamard (ancQubit n), Gate.measZ (ancQubit n)]) =
         ([Gate.prepPlus (ancQubit n)] ++
            (support.map fun q =>
              Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) ++
            [Gate.hadamard (ancQubit n)]) ++ [Gate.measZ (ancQubit n)]
        from by simp [List.append_assoc]]
  rw [propagateCircuit_append]
  -- After [...] (everything except measZ): anc.paulis = hadamardAction (productZPart support E);
  --                                       anc.measFlips = false.
  set body := [Gate.prepPlus (ancQubit n)] ++
              (support.map fun q =>
                Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) ++
              [Gate.hadamard (ancQubit n)]
  set esmid := propagateCircuit body (initialFromData E)
  have h_mf : esmid.measFlips (ancQubit n) = false :=
    prep_cnotChain_hadamard_measFlips support E
  -- Compute anc.paulis of esmid: it's hadamardAction (productZPart support E).
  have h_paulis : esmid.paulis (ancQubit n) = hadamardAction (productZPart support E) := by
    show (propagateCircuit ([_] ++ _ ++ [_]) (initialFromData E)).paulis (ancQubit n) = _
    rw [propagateCircuit_append, propagateCircuit_append]
    simp only [propagateCircuit]
    -- After prepPlus + chain: anc.paulis = productZPart support E (iter 14).
    set es1 := propagateGate (Gate.prepPlus (ancQubit n)) (initialFromData E)
    have hps : (propagateCircuit
                  (support.map fun q =>
                    Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) es1).paulis
                  (ancQubit n) = productZPart support E :=
      prep_cnotChain_anc_paulis support E
    -- After hadamard:
    set es2 := propagateCircuit (support.map _) es1
    have hes2 : es2.paulis (ancQubit n) = productZPart support E := hps
    simp only [propagateGate]
    rw [hes2]
    simp
  -- Now apply measZ: measFlips at anc = xor false (hasXComp anc.paulis).
  simp only [propagateCircuit, propagateGate]
  show (if ancQubit n = ancQubit n then _ else _) = _
  rw [if_pos rfl, h_paulis]
  show xor (esmid.measFlips (ancQubit n)) _ = _
  rw [h_mf]
  simp

/-! ## Connection between `productZPart` / `hadamardAction` and
   `ErrorVec.parity` — full C1 -/

/-- `hadamardAction p` for `p ∈ {I, Z}`: I → I, Z → X. -/
private theorem hadamardAction_of_IZ (p : Pauli) (hp : p = .I ∨ p = .Z) :
    hadamardAction p = if p = .Z then Pauli.X else Pauli.I := by
  rcases hp with rfl | rfl <;> simp [hadamardAction]

/-- `hasXComp (hadamardAction p)` for `p ∈ {I, Z}`. -/
private theorem hasXComp_hadamardAction_IZ (p : Pauli) (hp : p = .I ∨ p = .Z) :
    hasXComp (hadamardAction p) = decide (p = .Z) := by
  rcases hp with rfl | rfl <;> simp [hadamardAction, hasXComp]

/-- Boolean parity over a list: xor over a predicate. -/
def listZParity {n : Nat} (qs : List (Fin n)) (E : ErrorVec n) : Bool :=
  qs.foldr (fun q b => xor (decide (zPart (E q) = .Z)) b) false

@[simp] theorem listZParity_nil {n : Nat} (E : ErrorVec n) :
    listZParity ([] : List (Fin n)) E = false := rfl

@[simp] theorem listZParity_cons {n : Nat} (q : Fin n) (qs : List (Fin n))
    (E : ErrorVec n) :
    listZParity (q :: qs) E = xor (decide (zPart (E q) = .Z)) (listZParity qs E) := rfl

theorem productZPart_eq_Z_iff_listZParity {n : Nat}
    (qs : List (Fin n)) (E : ErrorVec n) :
    productZPart qs E = Pauli.Z ↔ listZParity qs E = true := by
  induction qs with
  | nil => simp [productZPart, listZParity]
  | cons q rest ih =>
    simp only [productZPart_cons, listZParity_cons]
    rcases zPart_in_IZ (E q) with hzq | hzq <;>
      rcases productZPart_in_IZ rest E with hp | hp
    · -- zPart (E q) = I, productZPart rest = I
      rw [hzq, hp]
      have hl : listZParity rest E = false := by
        rcases Bool.eq_false_or_eq_true (listZParity rest E) with h | h
        · exfalso
          have := ih.mpr h; rw [this] at hp; exact Pauli.noConfusion hp
        · exact h
      simp [pauliMul, hl]
    · -- zPart (E q) = I, productZPart rest = Z
      rw [hzq, hp]
      have hl : listZParity rest E = true := ih.mp hp
      simp [pauliMul, hl]
    · -- zPart (E q) = Z, productZPart rest = I
      rw [hzq, hp]
      have hl : listZParity rest E = false := by
        rcases Bool.eq_false_or_eq_true (listZParity rest E) with h | h
        · exfalso
          have := ih.mpr h; rw [this] at hp; exact Pauli.noConfusion hp
        · exact h
      simp [pauliMul, hl]
    · -- zPart (E q) = Z, productZPart rest = Z
      rw [hzq, hp]
      have hl : listZParity rest E = true := ih.mp hp
      simp [pauliMul, hl]

/-! ## ErrorVec.parity ↔ listZParity (under Nodup support) -/

/-- The "anticommutes with X" predicate is equivalent to "has Z-component". -/
private theorem anticommutes_X_iff_zPart_Z (p : Pauli) :
    Pauli.anticommutes Pauli.X p = decide (zPart p = Pauli.Z) := by
  cases p <;> decide

/-- For `i ∉ support`, `Xstabilizer support i = .I` and so it commutes
    with anything. -/
theorem Xstabilizer_anticommutes_not_mem {n : Nat} (support : List (Fin n))
    (i : Fin n) (h : i ∉ support) (p : Pauli) :
    Pauli.anticommutes (Xstabilizer support i) p = false := by
  unfold Xstabilizer
  rw [if_neg h]
  simp [Pauli.anticommutes]

/-- For `i ∈ support`, `Xstabilizer support i = .X` so anticommutes
    with `p` iff `p` has Z-component. -/
theorem Xstabilizer_anticommutes_mem {n : Nat} (support : List (Fin n))
    (i : Fin n) (h : i ∈ support) (p : Pauli) :
    Pauli.anticommutes (Xstabilizer support i) p = decide (zPart p = Pauli.Z) := by
  unfold Xstabilizer
  rw [if_pos h]
  exact anticommutes_X_iff_zPart_Z p

-- **Filter set decomposition** (cons case) is the planned next step
-- toward `parity_Xstabilizer_eq_listZParity`. The decomposition splits
-- the anticommutes-filter set for `q :: rest` into the rest's filter
-- plus the singleton `{q}` (conditioned on whether `anticommutes X (E q)`).
-- Initial attempt in iter 17 hit Finset.mem_filter / if-then-else
-- elaboration issues for the `i ≠ q ∧ i ∈ rest` case. Deferring to
-- iter 18 with a different proof strategy (direct cardinality via
-- `Finset.card_filter` and `Finset.sum_ite`).

end QStab.Compiler.SchemeCorrectStandard
