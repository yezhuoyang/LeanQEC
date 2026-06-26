import QStab.QClifford.ToleratesFaults

/-! # A concrete fault-tolerance theorem (input-fault model)

`barrier_tolerates` (in `FaultHoare.lean`) requires a *state-only* barrier
preserved by *every gate*. That cannot hold for a syndrome-extraction
circuit under mid-circuit faults: a fault on the ancilla, propagated by a
later `CNOT(anc, data)`, changes the data error (a *hook*), so no
state-only measure on the data is gate-invariant. Capturing hooks is
exactly what the QStab back-action machinery does; transporting it gives
the *full* mid-circuit result and is the subject of the QStab→QClifford
simulation bridge (future work).

This file delivers what *is* cleanly provable now: a concrete,
non-vacuous fault-tolerance theorem for the **input-fault model**, where
the error locations sit at the *start* of the circuit. The key enabling
fact is that a real syndrome-extraction circuit preserves the data error
**end-to-end** for an arbitrary input state (each gadget's `prepPlus`
resets the ancilla); e.g. `toCircuitX_dataPauli_eq`. We phrase the result
against an abstract logical-distance measure `μ`, so the surface
instantiation only has to supply `μ = weight ∘ dataPauli`, its
preservation lemma (already proved as `toCircuitX_weight_eq`), and the
code's minimum-distance property.
-/

namespace QStab.QClifford

/-- Embed a fault-free gate circuit as an instrumented circuit. -/
def gateInstrs {nq : Nat} (c : Circuit nq) : FCircuit nq := c.map FInstr.gate

/-- A prefix of error locations on the listed qubits. -/
def errLocs {nq : Nat} (qs : List (Fin nq)) : FCircuit nq := qs.map FInstr.errLoc

@[simp] theorem eraseFaults_gateInstrs {nq : Nat} (c : Circuit nq) :
    eraseFaults (gateInstrs c) = c := by
  induction c with
  | nil => rfl
  | cons g gs ih =>
      show eraseFaults (FInstr.gate g :: gateInstrs gs) = g :: gs
      rw [eraseFaults_gate, ih]

/-- An execution of a fault-free (`gateInstrs`) circuit injects nothing
    (`w = 0`) and equals the deterministic propagation. -/
theorem fcevalW_gateInstrs {nq : Nat} {w : Nat} {c : Circuit nq}
    {es es' : ErrorState nq} (h : fcevalW w (gateInstrs c) es es') :
    w = 0 ∧ es' = propagateCircuit c es := by
  induction c generalizing w es with
  | nil =>
      simp only [gateInstrs, List.map_nil] at h
      cases h with | nil => exact ⟨rfl, rfl⟩
  | cons g gs ih =>
      simp only [gateInstrs, List.map_cons] at h
      cases h with
      | gate g2 is2 es2 esf2 w2 hpre =>
          obtain ⟨hw, hes⟩ := ih hpre
          exact ⟨hw, hes⟩

/-- An execution of `fc1 ++ fc2` splits into an `fc1`-run and an
    `fc2`-run with the fault counts adding. -/
theorem fcevalW_append_inv {nq : Nat} {w : Nat} {fc1 fc2 : FCircuit nq}
    {es es' : ErrorState nq} (h : fcevalW w (fc1 ++ fc2) es es') :
    ∃ w1 w2 em, w1 + w2 = w ∧ fcevalW w1 fc1 es em ∧ fcevalW w2 fc2 em es' := by
  induction fc1 generalizing w es with
  | nil =>
      exact ⟨0, w, es, by omega, fcevalW.nil es, by simpa using h⟩
  | cons i rest ih =>
      simp only [List.cons_append] at h
      cases h with
      | gate g2 is2 es2 esf2 w2 hpre =>
          obtain ⟨w1', w2', em, hsum, hr1, hr2⟩ := ih hpre
          exact ⟨w1', w2', em, hsum, fcevalW.gate g2 rest es em w1' hr1, hr2⟩
      | idle q2 is2 es2 esf2 w2 hpre =>
          obtain ⟨w1', w2', em, hsum, hr1, hr2⟩ := ih hpre
          exact ⟨w1', w2', em, hsum, fcevalW.idle q2 rest es em w1' hr1, hr2⟩
      | inject q2 is2 es2 esf2 p hp w2 hpre =>
          obtain ⟨w1', w2', em, hsum, hr1, hr2⟩ := ih hpre
          exact ⟨w1' + 1, w2', em, by omega,
                 fcevalW.inject q2 rest es em p hp w1' hr1, hr2⟩

/-- An error-location prefix raises an abstract measure `μ` by at most
    the fault count, given `μ` rises by at most `1` per injection. -/
theorem errLocs_mu_bound {nq : Nat} (μ : ErrorState nq → Nat)
    (hinject : ∀ (es : ErrorState nq) (q : Fin nq) (p : Pauli),
        μ (es.inject q p) ≤ μ es + 1)
    {w : Nat} {qs : List (Fin nq)} {es es' : ErrorState nq}
    (h : fcevalW w (errLocs qs) es es') : μ es' ≤ μ es + w := by
  induction qs generalizing w es with
  | nil =>
      simp only [errLocs, List.map_nil] at h
      cases h with | nil => simp
  | cons q rest ih =>
      simp only [errLocs, List.map_cons] at h
      cases h with
      | idle q2 is2 es2 esf2 w2 hpre =>
          have := ih hpre; omega
      | inject q2 is2 es2 esf2 p hp w2 hpre =>
          have hih := ih hpre
          have hinj := hinject es q p
          omega

/-- **Concrete fault tolerance (input-fault model).** With error
    locations `qs` at the start followed by a circuit `circ` that
    preserves a logical-distance measure `μ`, the instrumented circuit
    tolerates every `t < d` faults against any failure predicate whose
    states have `μ ≥ d`.

    For the surface code: `μ = weight ∘ dataPauli`, `hpreserve` is
    `toCircuitX_weight_eq`, and `hfail` is the code's minimum-distance
    property (`d`-weight floor on nontrivial logical operators). -/
theorem input_fault_tolerant {nq : Nat}
    (circ : Circuit nq) (qs : List (Fin nq))
    (μ : ErrorState nq → Nat)
    (hclean : μ (ErrorState.clean nq) = 0)
    (hinject : ∀ (es : ErrorState nq) (q : Fin nq) (p : Pauli),
        μ (es.inject q p) ≤ μ es + 1)
    (hpreserve : ∀ es, μ (propagateCircuit circ es) = μ es)
    (failure : ErrorState nq → Prop) (d : Nat)
    (hfail : ∀ es, failure es → d ≤ μ es)
    (t : Nat) (ht : t < d) :
    ToleratesFaults (errLocs qs ++ gateInstrs circ) failure t := by
  intro w es' hw hev hfailes
  obtain ⟨w1, w2, em, hsum, h1, h2⟩ := fcevalW_append_inv hev
  have hmu_em : μ em ≤ μ (ErrorState.clean nq) + w1 := errLocs_mu_bound μ hinject h1
  rw [hclean] at hmu_em
  obtain ⟨_, hes'⟩ := fcevalW_gateInstrs h2
  have hmu_es' : μ es' = μ em := by rw [hes']; exact hpreserve em
  have hd : d ≤ μ es' := hfail es' hfailes
  omega

end QStab.QClifford
