import QStab.QClifford.ToleratesFaults

/-! # Decidable fault-tolerance by outcome enumeration

For a **concrete** instrumented circuit the fault model is finite: each
error location independently does nothing or injects one of `X,Y,Z`. So
the set of `(fault-count, final-state)` outcomes is a finite, computable
list (`allFaultRuns`), and `ToleratesFaults` reduces to a finite check
over that list (`tolerates_iff`). With a decidable failure predicate the
whole statement is `Decidable`, so concrete instances are dischargeable
by `decide`/`native_decide`.

This is the engine the automatic compiler will target: emit the circuit +
failure predicate, and the FT certificate is a `decide`. It also lets us
gain confidence on concrete small codes (5-qubit, Steane, surface d=3)
before automating. -/

namespace QStab.QClifford

/-- All `(fault-count, final-state)` outcomes of running `fc` from `es`
    under the non-deterministic fault model. At a gate: propagate. At an
    error location: branch into idle plus one branch per injected Pauli
    `X,Y,Z`, each costing one fault. -/
def allFaultRuns {nq : Nat} : FCircuit nq → ErrorState nq → List (Nat × ErrorState nq)
  | [], es => [(0, es)]
  | .gate g :: rest, es => allFaultRuns rest (propagateGate g es)
  | .errLoc q :: rest, es =>
      allFaultRuns rest es ++
      ([Pauli.X, Pauli.Y, Pauli.Z].flatMap fun p =>
        (allFaultRuns rest (es.inject q p)).map (fun we => (we.1 + 1, we.2)))

/-- Every fault execution appears in `allFaultRuns`. -/
theorem mem_of_fcevalW {nq : Nat} {w : Nat} {fc : FCircuit nq} {es es' : ErrorState nq}
    (h : fcevalW w fc es es') : (w, es') ∈ allFaultRuns fc es := by
  induction h with
  | nil es => simp [allFaultRuns]
  | gate g is es esf w hpre ih => simpa [allFaultRuns] using ih
  | idle q is es esf w hpre ih =>
      simp only [allFaultRuns]
      exact List.mem_append_left _ ih
  | inject q is es esf p hp w hpre ih =>
      simp only [allFaultRuns]
      refine List.mem_append_right _ ?_
      simp only [List.mem_flatMap, List.mem_map]
      exact ⟨p, by cases p <;> simp_all, (w, esf), ih, rfl⟩

/-- Conversely, every entry of `allFaultRuns` is a genuine fault execution. -/
theorem fcevalW_of_mem {nq : Nat} {fc : FCircuit nq} {w : Nat} {es es' : ErrorState nq}
    (h : (w, es') ∈ allFaultRuns fc es) : fcevalW w fc es es' := by
  induction fc generalizing w es es' with
  | nil =>
      simp only [allFaultRuns, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨hw, he⟩ := h; subst hw; subst he; exact fcevalW.nil _
  | cons instr rest ih =>
      cases instr with
      | gate g =>
          simp only [allFaultRuns] at h
          exact fcevalW.gate g rest es es' w (ih h)
      | errLoc q =>
          simp only [allFaultRuns, List.mem_append, List.mem_flatMap, List.mem_map] at h
          rcases h with hidle | ⟨p, hpm, we, hmem, heq⟩
          · exact fcevalW.idle q rest es es' w (ih hidle)
          · obtain ⟨w', e'⟩ := we
            simp only [Prod.mk.injEq] at heq
            obtain ⟨hw, he⟩ := heq; subst hw; subst he
            have hpne : p ≠ Pauli.I := by intro hh; subst hh; simp at hpm
            exact fcevalW.inject q rest es e' p hpne w' (ih hmem)

/-- **Fault tolerance as a finite check.** Tolerating `t` faults is
    equivalent to: no enumerated outcome of weight `≤ t` is a failure. -/
theorem tolerates_iff {nq : Nat} (fc : FCircuit nq)
    (failure : ErrorState nq → Prop) (t : Nat) :
    ToleratesFaults fc failure t ↔
    ∀ p ∈ allFaultRuns fc (ErrorState.clean nq), p.1 ≤ t → ¬ failure p.2 := by
  constructor
  · intro h p hp hpt
    obtain ⟨w, es'⟩ := p
    exact h w es' hpt (fcevalW_of_mem hp)
  · intro h w es' hwt hev
    exact h (w, es') (mem_of_fcevalW hev) hwt

/-! ## Validation: the framework discharges concrete instances by `decide` -/

section Validation

/-- A fault-free fragment tolerates any number of faults against a
    condition the clean output does not meet. -/
example : ToleratesFaults [FInstr.gate (Gate.hadamard (0 : Fin 2))]
    (fun es => es.paulis 0 = Pauli.X) 5 := by
  rw [tolerates_iff]; decide

/-- A bare error location tolerates `0` faults against "X on qubit 0"... -/
example : ToleratesFaults [FInstr.errLoc (0 : Fin 2)]
    (fun es => es.paulis 0 = Pauli.X) 0 := by
  rw [tolerates_iff]; decide

/-- ...but NOT `1` fault: the `X`-injection branch triggers the failure.
    The framework correctly refutes over-optimistic claims. -/
example : ¬ ToleratesFaults [FInstr.errLoc (0 : Fin 2)]
    (fun es => es.paulis 0 = Pauli.X) 1 := by
  rw [tolerates_iff]; decide

end Validation

end QStab.QClifford
