import QStab.QClifford.InputFaultFT
import QStab.Compiler.ToCircuit
import QStab.Examples.CompilerTest

/-! # Concrete input-fault fault tolerance for the surface d=3 X-circuit

Instantiates the scheme-generic `input_fault_tolerant` (with the
logical-distance measure `μ = dataWt`, i.e. data-qubit Pauli weight) on
the actual compiled surface d=3 X-side circuit `toCircuitX surfaceD3Spec`.
The data-preservation hypothesis is discharged by the proved
`toCircuitX_weight_eq`; the code's minimum-distance property enters as the
`hfail` field (`failure ⇒ d ≤ dataWt`), a code-spec assumption.

This is a *concrete, non-vacuous* gate-level FT theorem: it bounds the
residual logical weight by the injected-fault count for faults placed at
the circuit input. Mid-circuit (hook) faults need the full `align`
obligation of `GateBarrierCert` (the perpendicular-spread argument),
which is the remaining geometric work.
-/

namespace QStab.QClifford

open QStab QStab.Compiler QStab.QClifford.Standard QStab.Paper.Soundness

/-- The clean state has data weight `0`. -/
theorem dataWt_clean (n : Nat) : dataWt n (ErrorState.clean (n + 1)) = 0 := by
  simp [dataWt, dataErr, ErrorState.clean]

/-- A single injection raises the data weight by at most `1`. -/
theorem dataWt_inject_le (n : Nat) (es : ErrorState (n + 1)) (q : Fin (n + 1))
    (p : Pauli) : dataWt n (es.inject q p) ≤ dataWt n es + 1 := by
  unfold dataWt
  by_cases hq : q.val < n
  · have hsub :
        (Finset.univ.filter fun i : Fin n => dataErr n (es.inject q p) i ≠ .I) ⊆
        insert (⟨q.val, hq⟩ : Fin n)
          (Finset.univ.filter fun i : Fin n => dataErr n es i ≠ .I) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_cases hii : i = (⟨q.val, hq⟩ : Fin n)
      · exact hii ▸ Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hne : (⟨i.val, by omega⟩ : Fin (n + 1)) ≠ q := by
          intro h
          exact hii (Fin.ext (by have := congrArg Fin.val h; simpa using this))
        have heq : dataErr n (es.inject q p) i = dataErr n es i := by
          simp only [dataErr, ErrorState.inject, if_neg hne]
        rwa [heq] at hi
    exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
  · refine le_trans (Finset.card_le_card ?_) (Nat.le_succ _)
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hne : (⟨i.val, by omega⟩ : Fin (n + 1)) ≠ q := by
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    have heq : dataErr n (es.inject q p) i = dataErr n es i := by
      simp only [dataErr, ErrorState.inject, if_neg hne]
    rwa [heq] at hi

/-- **Input-fault FT for any data-`dataWt`-preserving circuit.** -/
theorem dataWt_input_fault_tolerant {n : Nat} (circ : Circuit (n + 1))
    (qs : List (Fin (n + 1)))
    (hpres : ∀ es, dataWt n (propagateCircuit circ es) = dataWt n es)
    (failure : ErrorState (n + 1) → Prop) (d : Nat)
    (hfail : ∀ es, failure es → d ≤ dataWt n es) (t : Nat) (ht : t < d) :
    ToleratesFaults (errLocs qs ++ gateInstrs circ) failure t :=
  input_fault_tolerant circ qs (dataWt n) (dataWt_clean n) (dataWt_inject_le n)
    hpres failure d hfail t ht

/-- The full surface X-circuit preserves data weight (from
    `toCircuitX_weight_eq` via `dataPauli_weight_eq`). -/
theorem toCircuitX_dataWt_eq (spec : CodeSpec) (es : ErrorState (spec.n + 1)) :
    dataWt spec.n (propagateCircuit (toCircuitX spec) es) = dataWt spec.n es := by
  rw [← dataPauli_weight_eq spec.n, ← dataPauli_weight_eq spec.n]
  exact toCircuitX_weight_eq spec es

/-- **Concrete surface d=3 input-fault tolerance.** With error locations
    `qs` at the input, the compiled surface d=3 X-circuit tolerates every
    `t < d` faults against any failure predicate whose states carry data
    weight `≥ d` (the code's minimum-distance property; `d = 3` for the
    surface code, so it tolerates `2` input faults). -/
theorem surface_d3_input_fault_tolerant
    (qs : List (Fin (surfaceD3Spec.n + 1)))
    (failure : ErrorState (surfaceD3Spec.n + 1) → Prop) (d : Nat)
    (hfail : ∀ es, failure es → d ≤ dataWt surfaceD3Spec.n es)
    (t : Nat) (ht : t < d) :
    ToleratesFaults (errLocs qs ++ gateInstrs (toCircuitX surfaceD3Spec)) failure t :=
  dataWt_input_fault_tolerant (toCircuitX surfaceD3Spec) qs
    (toCircuitX_dataWt_eq surfaceD3Spec) failure d hfail t ht

end QStab.QClifford
