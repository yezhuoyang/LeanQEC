import QStab.Compiler.SchemeCorrectStandard

/-! # Z-side gadget correctness: `zCircuit_SchemeCorrect`

Mirror of `SchemeCorrectStandard.lean`'s X-side, proving:
- **C1 (parityFaithful)** for `zCircuit` measuring `Zstabilizer support`.
- **C2 (noBackAction)** — already proven as `zCircuit_noBackAction`.
- **C3 (boundedHook)** — already proven via `weight_bounded_z`.
- **Strong data preservation** (`zCircuit_data_preserved_general`) —
  data preserved for any input state (not just `initialFromData E`).

Packages into `zCircuit_SchemeCorrect` analogous to `xCircuit_SchemeCorrect`.

The Z-scheme is the dual of X-scheme: `CNOT(data q, anc)` propagates
`xPart(E q)` to the ancilla. Without a final Hadamard, the ancilla's
accumulated `productXPart support E` is read directly by `measZ` as
the parity bit.
-/

namespace QStab.Compiler.SchemeCorrectStandard

open QStab QStab.QClifford QStab.QClifford.Standard QStab.Paper.Soundness ErrorVec

variable {n : Nat}

/-! ## After prepZero + CNOT chain: ancilla = `productXPart support E` -/

/-- After `prepZero(anc)` on `initialFromData E`, the ancilla has Pauli I. -/
theorem prepZero_anc_paulis_z (E : ErrorVec n) :
    (propagateGate (Gate.prepZero (ancQubit n)) (initialFromData E)).paulis
      (ancQubit n) = Pauli.I := by
  simp [propagateGate, ancQubit]

/-- The Z-side CNOT step: from anc paulis `p` and data q pauli `E q`,
    the new anc paulis = `pauliMul (xPart (E q)) p`. -/
theorem cnot_data_anc_anc_paulis_step (q : Fin n) (E : ErrorVec n)
    (es : ErrorState (n + 1))
    (h_data : ∀ i : Fin n, es.paulis (mkDataQubit n i) = E i) :
    (propagateGate (Gate.cnot (mkDataQubit n q) (ancQubit n)
                              (data_ne_anc n q)) es).paulis (ancQubit n) =
    pauliMul (xPart (E q)) (es.paulis (ancQubit n)) := by
  rw [cnot_data_to_anc_anc_paulis]
  rw [h_data]

/-- The Z-side CNOT preserves the data-pauli-match invariant when the
    ancilla has `ancHasNoZ` (Z-component of anc = I). -/
theorem cnot_data_anc_data_preserved (q : Fin n) (es : ErrorState (n + 1))
    (h_ancNoZ : ancHasNoZ n es) (i : Fin n) :
    (propagateGate (Gate.cnot (mkDataQubit n q) (ancQubit n) (data_ne_anc n q)) es).paulis
      (mkDataQubit n i) = es.paulis (mkDataQubit n i) := by
  simp only [propagateGate]
  have h_ne_anc : (mkDataQubit n i) ≠ ancQubit n := data_ne_anc n i
  rw [if_neg h_ne_anc]
  by_cases hiq : i = q
  · subst hiq
    rw [if_pos rfl]
    show pauliMul (zPart (es.paulis (ancQubit n))) (es.paulis (mkDataQubit n i)) =
         es.paulis (mkDataQubit n i)
    have h_anc_no_z : zPart (es.paulis (ancQubit n)) = Pauli.I := h_ancNoZ
    rw [h_anc_no_z]
    cases (es.paulis (mkDataQubit n i)) <;> rfl
  · rw [if_neg (by
      intro h_eq
      apply hiq
      have : (mkDataQubit n i).val = (mkDataQubit n q).val :=
        congrArg Fin.val h_eq
      simp [mkDataQubit] at this
      exact Fin.ext this)]

/-- Induction over support: after `prepZero + CNOT chain`, the ancilla
    has Pauli `productXPart support E`. Critically uses that the
    ancilla has `ancHasNoZ` (preserved through the chain), so Z-side
    propagation doesn't introduce phantom Z-flux. -/
theorem cnotChain_anc_paulis_z (qs : List (Fin n)) (E : ErrorVec n)
    (es : ErrorState (n + 1))
    (h_data : ∀ i : Fin n, es.paulis (mkDataQubit n i) = E i)
    (h_ancNoZ : ancHasNoZ n es) :
    (propagateCircuit
      (qs.map fun q => Gate.cnot (mkDataQubit n q) (ancQubit n) (data_ne_anc n q))
      es).paulis (ancQubit n) =
    pauliMul (productXPart qs E) (es.paulis (ancQubit n)) := by
  induction qs generalizing es with
  | nil =>
    show es.paulis (ancQubit n) = pauliMul Pauli.I (es.paulis (ancQubit n))
    cases es.paulis (ancQubit n) <;> rfl
  | cons q rest ih =>
    simp only [List.map, propagateCircuit]
    set g := Gate.cnot (mkDataQubit n q) (ancQubit n) (data_ne_anc n q)
    set es' := propagateGate g es
    have h_data' : ∀ i : Fin n, es'.paulis (mkDataQubit n i) = E i := by
      intro i
      rw [cnot_data_anc_data_preserved q es h_ancNoZ i]
      exact h_data i
    have h_ancNoZ' : ancHasNoZ n es' :=
      (QStab.QClifford.Standard.cnot_data_anc_ancHasNoZ n q es h_ancNoZ).1
    rw [ih es' h_data' h_ancNoZ']
    rw [productXPart_cons]
    have h_es' : es'.paulis (ancQubit n) =
                 pauliMul (xPart (E q)) (es.paulis (ancQubit n)) :=
      cnot_data_anc_anc_paulis_step q E es h_data
    rw [h_es']
    -- Reduce: pauliMul (productXPart rest E) (pauliMul (xPart (E q)) p) =
    --         pauliMul (pauliMul (xPart (E q)) (productXPart rest E)) p.
    -- All three operands are in {I, X} (or es.paulis anc could be any),
    -- but pauliMul is associative.
    rcases productXPart_in_IX rest E with h1 | h1 <;>
      rcases xPart_in_IX (E q) with h2 | h2 <;>
      cases es.paulis (ancQubit n) <;>
      simp [h1, h2, pauliMul]

/-- The combined "prepZero + CNOT chain → ancilla = productXPart" lemma. -/
theorem prep_cnotChain_anc_paulis_z (support : List (Fin n)) (E : ErrorVec n) :
    (propagateCircuit
      ([Gate.prepZero (ancQubit n)] ++
       support.map fun q => Gate.cnot (mkDataQubit n q) (ancQubit n) (data_ne_anc n q))
      (initialFromData E)).paulis (ancQubit n) =
    productXPart support E := by
  rw [propagateCircuit_append]
  simp only [propagateCircuit]
  set es1 := propagateGate (Gate.prepZero (ancQubit n)) (initialFromData E)
  have h_anc1 : es1.paulis (ancQubit n) = Pauli.I := prepZero_anc_paulis_z E
  have h_ancNoZ1 : ancHasNoZ n es1 := ancHasNoZ_prepZero_anc (initialFromData E)
  have h_data1 : ∀ i : Fin n, es1.paulis (mkDataQubit n i) = E i := by
    intro i
    show (propagateGate (Gate.prepZero (ancQubit n)) (initialFromData E)).paulis
         (mkDataQubit n i) = E i
    simp only [propagateGate]
    rw [if_neg (data_ne_anc n i)]
    simp [initialFromData, mkDataQubit]
  rw [cnotChain_anc_paulis_z support E es1 h_data1 h_ancNoZ1]
  rw [h_anc1]
  cases productXPart support E <;> rfl

/-! ## measFlips remain false through prep + chain (so final mflip
    just reads the ancilla's X-component) -/

private theorem prepZero_preserves_measFlips (q : Fin (n+1))
    (es : ErrorState (n+1)) :
    (propagateGate (Gate.prepZero q) es).measFlips = es.measFlips := by
  simp [propagateGate]

private theorem cnot_preserves_measFlips (c t : Fin (n+1)) (hne : c ≠ t)
    (es : ErrorState (n+1)) :
    (propagateGate (Gate.cnot c t hne) es).measFlips = es.measFlips := by
  simp [propagateGate]

theorem prep_cnotChain_measFlips_z (support : List (Fin n)) (E : ErrorVec n) :
    (propagateCircuit
      ([Gate.prepZero (ancQubit n)] ++
       support.map fun q => Gate.cnot (mkDataQubit n q) (ancQubit n) (data_ne_anc n q))
      (initialFromData E)).measFlips (ancQubit n) = false := by
  rw [propagateCircuit_append]
  simp only [propagateCircuit]
  -- propagate through prepZero
  have h0 : (propagateGate (Gate.prepZero (ancQubit n)) (initialFromData E)).measFlips =
            (initialFromData E).measFlips := prepZero_preserves_measFlips _ _
  -- propagate through CNOT chain — induction
  suffices h_chain : ∀ qs : List (Fin n),
      ∀ es' : ErrorState (n+1),
      (propagateCircuit
        (qs.map fun q => Gate.cnot (mkDataQubit n q) (ancQubit n) (data_ne_anc n q)) es').measFlips =
      es'.measFlips by
    rw [h_chain]
    rw [h0]
    simp [initialFromData]
  intro qs
  induction qs with
  | nil => intro es'; simp [propagateCircuit]
  | cons q rest ih =>
      intro es'
      simp only [List.map, propagateCircuit]
      have := cnot_preserves_measFlips (mkDataQubit n q) (ancQubit n) (data_ne_anc n q) es'
      rw [ih, this]

/-! ## measFlipped after the full zCircuit = hasXComp of accumulated -/

theorem zCircuit_measFlipped_eq_hasXComp (support : List (Fin n)) (E : ErrorVec n) :
    measFlipped n (propagateCircuit (zCircuit n support) (initialFromData E))
    = hasXComp (productXPart support E) := by
  unfold zCircuit measFlipped
  -- zCircuit = [prepZero] ++ cnots ++ [measZ] = ([prepZero] ++ cnots) ++ [measZ]
  rw [show ([Gate.prepZero (ancQubit n)] ++
            (support.map fun q =>
              Gate.cnot (mkDataQubit n q) (ancQubit n) (data_ne_anc n q)) ++
            [Gate.measZ (ancQubit n)]) =
         ([Gate.prepZero (ancQubit n)] ++
            (support.map fun q =>
              Gate.cnot (mkDataQubit n q) (ancQubit n) (data_ne_anc n q))) ++
            [Gate.measZ (ancQubit n)]
        from by simp [List.append_assoc]]
  rw [propagateCircuit_append]
  set body := [Gate.prepZero (ancQubit n)] ++
              (support.map fun q =>
                Gate.cnot (mkDataQubit n q) (ancQubit n) (data_ne_anc n q))
  set esmid := propagateCircuit body (initialFromData E)
  have h_mf : esmid.measFlips (ancQubit n) = false :=
    prep_cnotChain_measFlips_z support E
  have h_paulis : esmid.paulis (ancQubit n) = productXPart support E :=
    prep_cnotChain_anc_paulis_z support E
  -- After measZ: measFlips at anc = xor old_mf (hasXComp anc.paulis).
  simp only [propagateCircuit, propagateGate]
  show (if ancQubit n = ancQubit n then _ else _) = _
  rw [if_pos rfl, h_paulis]
  show xor (esmid.measFlips (ancQubit n)) _ = _
  rw [h_mf]
  simp

/-! ## listXParity: bit-parity over `xPart` components -/

def listXParity (qs : List (Fin n)) (E : ErrorVec n) : Bool :=
  qs.foldr (fun q b => xor (decide (xPart (E q) = .X)) b) false

@[simp] theorem listXParity_nil (E : ErrorVec n) :
    listXParity ([] : List (Fin n)) E = false := rfl

@[simp] theorem listXParity_cons (q : Fin n) (qs : List (Fin n)) (E : ErrorVec n) :
    listXParity (q :: qs) E = xor (decide (xPart (E q) = .X)) (listXParity qs E) := rfl

theorem productXPart_eq_X_iff_listXParity (qs : List (Fin n)) (E : ErrorVec n) :
    productXPart qs E = Pauli.X ↔ listXParity qs E = true := by
  induction qs with
  | nil => simp [productXPart, listXParity]
  | cons q rest ih =>
    simp only [productXPart_cons, listXParity_cons]
    rcases xPart_in_IX (E q) with hxq | hxq <;>
      rcases productXPart_in_IX rest E with hp | hp
    · rw [hxq, hp]
      have hl : listXParity rest E = false := by
        rcases Bool.eq_false_or_eq_true (listXParity rest E) with h | h
        · exfalso
          have := ih.mpr h; rw [this] at hp; exact Pauli.noConfusion hp
        · exact h
      simp [pauliMul, hl]
    · rw [hxq, hp]
      have hl : listXParity rest E = true := ih.mp hp
      simp [pauliMul, hl]
    · rw [hxq, hp]
      have hl : listXParity rest E = false := by
        rcases Bool.eq_false_or_eq_true (listXParity rest E) with h | h
        · exfalso
          have := ih.mpr h; rw [this] at hp; exact Pauli.noConfusion hp
        · exact h
      simp [pauliMul, hl]
    · rw [hxq, hp]
      have hl : listXParity rest E = true := ih.mp hp
      simp [pauliMul, hl]

theorem hasXComp_of_in_IX (p : Pauli) (hp : p = Pauli.I ∨ p = Pauli.X) :
    hasXComp p = decide (p = Pauli.X) := by
  rcases hp with rfl | rfl <;> simp [hasXComp]

/-! ## Zstabilizer + anticommutation lemmas (mirror of Xstabilizer) -/

def Zstabilizer (support : List (Fin n)) : ErrorVec n :=
  fun i => if i ∈ support then Pauli.Z else Pauli.I

private theorem anticommutes_Z_iff_xPart_X (p : Pauli) :
    Pauli.anticommutes Pauli.Z p = decide (xPart p = Pauli.X) := by
  cases p <;> decide

theorem Zstabilizer_anticommutes_not_mem (support : List (Fin n))
    (i : Fin n) (h : i ∉ support) (p : Pauli) :
    Pauli.anticommutes (Zstabilizer support i) p = false := by
  unfold Zstabilizer
  rw [if_neg h]
  simp [Pauli.anticommutes]

theorem Zstabilizer_anticommutes_mem (support : List (Fin n))
    (i : Fin n) (h : i ∈ support) (p : Pauli) :
    Pauli.anticommutes (Zstabilizer support i) p = decide (xPart p = Pauli.X) := by
  unfold Zstabilizer
  rw [if_pos h]
  exact anticommutes_Z_iff_xPart_X p

theorem anticommutes_Zstabilizer_eq (support : List (Fin n))
    (E : ErrorVec n) (i : Fin n) :
    Pauli.anticommutes (Zstabilizer support i) (E i) =
      (decide (i ∈ support) && decide (xPart (E i) = Pauli.X)) := by
  by_cases h : i ∈ support
  · rw [Zstabilizer_anticommutes_mem support i h (E i)]
    simp [h]
  · rw [Zstabilizer_anticommutes_not_mem support i h (E i)]
    simp [h]

theorem parity_Zstabilizer_nil [NeZero n] (E : ErrorVec n) :
    ErrorVec.parity (Zstabilizer ([] : List (Fin n))) E = false := by
  unfold ErrorVec.parity
  have h : (Finset.univ.filter
      (fun i : Fin n => Pauli.anticommutes
        (Zstabilizer ([] : List (Fin n)) i) (E i))).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    have : Zstabilizer ([] : List (Fin n)) i = Pauli.I := by simp [Zstabilizer]
    rw [this]
    simp [Pauli.anticommutes]
  rw [h]; rfl

theorem Zstabilizer_filter_cons (q : Fin n) (rest : List (Fin n))
    (h_nm : q ∉ rest) (E : ErrorVec n) :
    (Finset.univ.filter
      (fun i : Fin n => Pauli.anticommutes (Zstabilizer (q :: rest) i) (E i))) =
    (Finset.univ.filter
      (fun i : Fin n => Pauli.anticommutes (Zstabilizer rest i) (E i)))
    ∪ (if xPart (E q) = Pauli.X then ({q} : Finset (Fin n)) else ∅) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
             Finset.mem_singleton]
  rw [anticommutes_Zstabilizer_eq, anticommutes_Zstabilizer_eq]
  by_cases hiq : i = q
  · subst hiq
    simp [h_nm]
    by_cases hx : xPart (E i) = Pauli.X
    · simp [hx]
    · simp [hx]
  · have hir : (i ∈ q :: rest) ↔ (i ∈ rest) := by simp [hiq]
    simp [hir, hiq]
    by_cases himem : i ∈ rest
    · by_cases hx : xPart (E i) = Pauli.X
      · simp [himem, hx]
      · simp [himem, hx]
        split_ifs <;> simp [hiq]
    · simp [himem]
      split_ifs <;> simp [hiq]

theorem Zstabilizer_filter_disjoint (q : Fin n) (rest : List (Fin n))
    (h_nm : q ∉ rest) (E : ErrorVec n) :
    Disjoint
      (Finset.univ.filter
        (fun i : Fin n => Pauli.anticommutes (Zstabilizer rest i) (E i)))
      (if xPart (E q) = Pauli.X then ({q} : Finset (Fin n)) else ∅) := by
  rw [Finset.disjoint_left]
  intro i hi_rest hi_sing
  split_ifs at hi_sing with h_x
  · rw [Finset.mem_singleton] at hi_sing
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi_rest
    rw [hi_sing] at hi_rest
    rw [Zstabilizer_anticommutes_not_mem rest q h_nm (E q)] at hi_rest
    exact (Bool.false_ne_true hi_rest).elim
  · cases hi_sing

theorem parity_Zstabilizer_cons (q : Fin n) (rest : List (Fin n))
    (h_nm : q ∉ rest) (E : ErrorVec n) :
    ErrorVec.parity (Zstabilizer (q :: rest)) E =
      (decide (xPart (E q) = Pauli.X) ^^ ErrorVec.parity (Zstabilizer rest) E) := by
  unfold ErrorVec.parity
  rw [Zstabilizer_filter_cons q rest h_nm E]
  rw [Finset.card_union_eq_card_add_card.mpr
        (Zstabilizer_filter_disjoint q rest h_nm E)]
  set rc := (Finset.univ.filter
              (fun i : Fin n => Pauli.anticommutes (Zstabilizer rest i) (E i))).card
  have h_sing_card :
      (if xPart (E q) = Pauli.X then ({q} : Finset (Fin n)) else ∅).card =
      (if xPart (E q) = Pauli.X then 1 else 0) := by
    split_ifs <;> simp
  rw [h_sing_card]
  by_cases hx : xPart (E q) = Pauli.X
  · simp only [hx, if_true, decide_true, Bool.true_xor]
    rcases Nat.mod_two_eq_zero_or_one rc with h | h <;> simp [Nat.add_mod, h]
  · simp only [hx, if_false, decide_false, Bool.false_xor, Nat.add_zero]

theorem parity_Zstabilizer_eq_listXParity [NeZero n]
    (support : List (Fin n)) (h_nodup : support.Nodup) (E : ErrorVec n) :
    ErrorVec.parity (Zstabilizer support) E = listXParity support E := by
  induction support with
  | nil => rw [parity_Zstabilizer_nil, listXParity_nil]
  | cons q rest ih =>
    have h_nm : q ∉ rest := List.Nodup.notMem h_nodup
    have h_rest_nodup : rest.Nodup := List.Nodup.of_cons h_nodup
    rw [parity_Zstabilizer_cons q rest h_nm E, listXParity_cons, ih h_rest_nodup]

/-! ## C1: zCircuit_parityFaithful -/

theorem zCircuit_parityFaithful [NeZero n] (support : List (Fin n))
    (h_nodup : support.Nodup) :
    parityFaithful (zCircuit n support) (Zstabilizer support) := by
  intro E
  show measFlipped n (propagateCircuit (zCircuit n support) (initialFromData E))
       = ErrorVec.parity (Zstabilizer support) E
  rw [zCircuit_measFlipped_eq_hasXComp,
      hasXComp_of_in_IX _ (productXPart_in_IX support E)]
  rw [parity_Zstabilizer_eq_listXParity support h_nodup E]
  by_cases h : productXPart support E = Pauli.X
  · rw [(productXPart_eq_X_iff_listXParity support E).mp h]
    simp [h]
  · have : listXParity support E = false := by
      rcases Bool.eq_false_or_eq_true (listXParity support E) with hl | hl
      · exact absurd ((productXPart_eq_X_iff_listXParity support E).mpr hl) h
      · exact hl
    rw [this]; simp [h]

/-! ## Strong data preservation: zCircuit on ANY input state preserves data -/

theorem zCircuit_data_preserved_general (support : List (Fin n))
    (es : ErrorState (n + 1)) :
    dataMatches (fun i => es.paulis ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                (propagateCircuit (zCircuit n support) es) := by
  set D : ErrorVec n := fun i => es.paulis ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ with hD
  have h_dm0 : dataMatches D es := fun i => rfl
  unfold zCircuit
  rw [propagateCircuit_append, propagateCircuit_append]
  have hpc1 : propagateCircuit [Gate.prepZero (ancQubit n)] es =
              propagateGate (Gate.prepZero (ancQubit n)) es := by
    simp [propagateCircuit]
  rw [hpc1]
  set es1 := propagateGate (Gate.prepZero (ancQubit n)) es
  have h_az1 : ancHasNoZ n es1 := ancHasNoZ_prepZero_anc es
  have h_dm1 : dataMatches D es1 :=
    dataMatches_prepZero_anc D es h_dm0
  obtain ⟨_, h_dm2⟩ := ancHasNoZ_dataMatches_zChain D support es1 h_az1 h_dm1
  set es2 := propagateCircuit
    (support.map fun q => Gate.cnot (mkDataQubit n q) (ancQubit n) (data_ne_anc n q)) es1
  simp only [propagateCircuit]
  -- After measZ on anc, data is preserved
  intro i
  simp only [propagateGate]
  exact h_dm2 i

/-- Corollary: dataPauli preservation in functional form (mirror of
    `xCircuit_dataPauli_preserved`). -/
theorem zCircuit_dataPauli_preserved (support : List (Fin n))
    (es : ErrorState (n + 1)) (i : Fin n) :
    (propagateCircuit (zCircuit n support) es).paulis
      ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ =
    es.paulis ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ :=
  zCircuit_data_preserved_general support es i

/-! ## C1 + C2 + C3 = SchemeCorrect for zCircuit -/

/-- **Z-side `SchemeCorrect`**: C1 (parityFaithful), C2 (noBackAction),
    C3 (boundedHook from `weight_bounded_z`) for `zCircuit n support`
    measuring `Zstabilizer support`. Under `support.Nodup` and
    `0 < support.length`, hook bound `r = support.length`. -/
theorem zCircuit_SchemeCorrect [NeZero n] (support : List (Fin n))
    (h_nodup : support.Nodup) (hs : 0 < support.length) :
    SchemeCorrect (zCircuit n support) (Zstabilizer support) support.length := by
  refine ⟨zCircuit_parityFaithful support h_nodup, zCircuit_noBackAction support, ?_⟩
  intro fault _
  rw [dataPauli_weight_eq]
  exact weight_bounded_z n support fault hs

end QStab.Compiler.SchemeCorrectStandard
