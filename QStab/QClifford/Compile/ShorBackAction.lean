import QStab.QClifford.Compile.ShorLeafClean

/-!
# Shor-scheme back-action characterization: the coupling-segment walk

Part 1 of the Shor site classification (`shor_gadget_site_classified`): the
gate-locality facts for the coupling segment and the two walk primitives.

The Shor gadget couples each scheduled data qubit to its **own** cat helper
(unlike NZ's shared ancilla), so a fault inside the coupling segment can only
ever reach that one slot's data qubit — every coupling-segment site has data
residual weight `≤ 1`.  The only weight-`2` residuals come from cascade-target
faults, whose cat Pauli vector the couplings then image onto data; that
transfer is `shorCouplings_from_catvec` (the C-vector walk): entering with
clean data and cats carrying `C`, each scheduled qubit ends at the hook value
`zPart (C cat)` (Z-kind) / `hadamardAction (zPart (C cat))` (X-kind), and
every other non-cat qubit is untouched.
-/

namespace QStab.QClifford.Compile

open QStab.QClifford

/-! ## Gate-locality of the coupling segment -/

/-- Every erased gate of a coupling slot acts only on the slot's data qubit or
its cat. -/
theorem shorCouplingSlot_gates_actOn {nq : Nat} (slot : ScheduledPauli nq) (cat : Fin nq)
    (g : Gate nq) (hg : g ∈ eraseFaults (shorCouplingSlot slot cat)) :
    ∀ q : Fin nq, gateActsOn g q → q = slot.qubit ∨ q = cat := by
  obtain ⟨sk, sq⟩ := slot
  intro q hq
  cases sk with
  | X =>
      by_cases hqc : sq = cat
      · simp [shorCouplingSlot, hadamard, cnot, hqc, eraseFaults] at hg
        rcases hg with rfl
        exact Or.inr hq
      · simp [shorCouplingSlot, hadamard, cnot, hqc, eraseFaults] at hg
        rcases hg with rfl | rfl | rfl
        · exact Or.inl hq
        · rcases hq with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · exact Or.inl hq
  | Z =>
      by_cases hqc : sq = cat
      · simp [shorCouplingSlot, cnot, hqc] at hg
      · simp [shorCouplingSlot, cnot, hqc, eraseFaults] at hg
        subst hg
        rcases hq with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl

/-- Every erased gate of the coupling chain acts only on some pair's qubits. -/
theorem shorCouplings_gates_actOn {nq : Nat} (pairs : List (ScheduledPauli nq × Fin nq))
    (g : Gate nq)
    (hg : g ∈ eraseFaults ((pairs.map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten)) :
    ∀ q : Fin nq, gateActsOn g q → ∃ pc ∈ pairs, q = pc.1.qubit ∨ q = pc.2 := by
  intro q hq
  rw [eraseFaults_flatten, List.map_map, List.mem_flatten] at hg
  obtain ⟨c, hc, hgc⟩ := hg
  rw [List.mem_map] at hc
  obtain ⟨pc, hpc, rfl⟩ := hc
  exact ⟨pc, hpc, shorCouplingSlot_gates_actOn pc.1 pc.2 g hgc q hq⟩

/-- **Off-pair locality**: propagating the coupling chain leaves every qubit
that is neither a scheduled data qubit nor a cat of any pair unchanged. -/
theorem shorCouplings_paulis_off {nq : Nat} (pairs : List (ScheduledPauli nq × Fin nq))
    (d : Fin nq) (hd : ∀ pc ∈ pairs, d ≠ pc.1.qubit ∧ d ≠ pc.2)
    (es : ErrorState nq) :
    (propagateCircuit (eraseFaults
        ((pairs.map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten)) es).paulis d
      = es.paulis d := by
  apply propagateCircuit_paulis_off
  intro g hg hact
  obtain ⟨pc, hpc, hq⟩ := shorCouplings_gates_actOn pairs g hg d hact
  rcases hq with rfl | rfl
  · exact (hd pc hpc).1 rfl
  · exact (hd pc hpc).2 rfl

/-- The trailing raw measurements followed by any tail: still Pauli-preserving
on data when the tail preserves data (composition helper). -/
theorem rawMeasZ_then_tail_data {P : QECParams} {total : Nat}
    (cs : List (Fin (P.n + total))) (tail : Circuit (P.n + total))
    (htail : ∀ (es : ErrorState (P.n + total)) (q'' : Fin P.n),
      (propagateCircuit tail es).paulis (freshDataQ P.n total q'') =
        es.paulis (freshDataQ P.n total q''))
    (es : ErrorState (P.n + total)) (q' : Fin P.n) :
    (propagateCircuit (eraseFaults ((cs.map rawMeasZ).flatten) ++ tail) es).paulis
        (freshDataQ P.n total q')
      = es.paulis (freshDataQ P.n total q') := by
  rw [QHL.Target.propagateCircuit_append, htail, rawMeasZ_flatten_paulis]

/-! ## The C-vector walk (cascade faults imaged onto data) -/

/-- The hook value a coupling slot of the given CSS kind transfers onto its
clean data qubit from a cat carrying `w`. -/
def couplingHook (k : XZPauli) (w : Pauli) : Pauli :=
  match k with
  | .Z => zPart w
  | .X => hadamardAction (zPart w)

/-- One coupling slot with a dirty cat: the (clean) data qubit ends at the
hook value, the cat's Z-part is what it transfers (its own final value is
irrelevant downstream — no later slot touches it). -/
theorem shorCouplingSlot_hook {nq : Nat} (slot : ScheduledPauli nq) (cat : Fin nq)
    (hqc : slot.qubit ≠ cat) (es : ErrorState nq) (w : Pauli)
    (hcat : es.paulis cat = w) (hq : es.paulis slot.qubit = Pauli.I) :
    (propagateCircuit (eraseFaults (shorCouplingSlot slot cat)) es).paulis slot.qubit
      = couplingHook slot.kind w := by
  obtain ⟨sk, sq⟩ := slot
  cases sk with
  | X =>
      have hc : eraseFaults (shorCouplingSlot ⟨.X, sq⟩ cat) =
          [Gate.hadamard sq, Gate.cnot sq cat hqc, Gate.hadamard sq] := by
        simp [shorCouplingSlot, hadamard, cnot, hqc, eraseFaults]
      rw [hc]
      simp only [propagateCircuit]
      have h1q : (propagateGate (Gate.hadamard sq) es).paulis sq = Pauli.I := by
        rw [propagateGate_hadamard_self, hq]; rfl
      have h1c : (propagateGate (Gate.hadamard sq) es).paulis cat = w := by
        rw [propagateGate_hadamard_paulis_ne sq es cat (Ne.symm hqc), hcat]
      rw [propagateGate_hadamard_self, propagateGate_cnot_control sq cat hqc, h1q, h1c]
      show hadamardAction (pauliMul (zPart w) Pauli.I) = couplingHook XZPauli.X w
      cases w <;> rfl
  | Z =>
      have hc : eraseFaults (shorCouplingSlot ⟨.Z, sq⟩ cat) = [Gate.cnot sq cat hqc] := by
        simp [shorCouplingSlot, cnot, hqc, eraseFaults]
      rw [hc]
      simp only [propagateCircuit]
      rw [propagateGate_cnot_control sq cat hqc, hcat, hq]
      show pauliMul (zPart w) Pauli.I = couplingHook XZPauli.Z w
      cases w <;> rfl

/-- One coupling slot touches only its own pair (restated for the walk). -/
theorem shorCouplingSlot_paulis_off {nq : Nat} (slot : ScheduledPauli nq) (cat : Fin nq)
    (d : Fin nq) (hdq : d ≠ slot.qubit) (hdc : d ≠ cat) (es : ErrorState nq) :
    (propagateCircuit (eraseFaults (shorCouplingSlot slot cat)) es).paulis d
      = es.paulis d := by
  apply propagateCircuit_paulis_off
  intro g hg hact
  rcases shorCouplingSlot_gates_actOn slot cat g hg d hact with rfl | rfl
  · exact hdq rfl
  · exact hdc rfl

/-- **The C-vector walk.**  Entering the coupling chain with clean data and
cats carrying the Pauli vector `C`, every pair's data qubit ends at its hook
value, and every qubit off the pairs is untouched.  Stated per scheduled pair;
`hqd` (pairwise-distinct data qubits) keeps later slots off earlier results. -/
theorem shorCouplings_from_catvec {nq : Nat} :
    ∀ (pairs : List (ScheduledPauli nq × Fin nq)) (es : ErrorState nq),
      ((pairs.map (·.2)).Nodup) →
      ((pairs.map (·.1.qubit)).Nodup) →
      (∀ pc ∈ pairs, ∀ pc' ∈ pairs, pc.1.qubit ≠ pc'.2) →
      (∀ pc ∈ pairs, es.paulis pc.1.qubit = Pauli.I) →
      ∀ pc ∈ pairs,
        (propagateCircuit (eraseFaults
            ((pairs.map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten)) es).paulis pc.1.qubit
          = couplingHook pc.1.kind (es.paulis pc.2) := by
  intro pairs
  induction pairs with
  | nil => intro es _ _ _ _ pc hpc; exact absurd hpc (List.not_mem_nil)
  | cons p0 rest ih =>
      intro es hndc hndq hqc hclean pc hpc
      have hcirc : eraseFaults (((p0 :: rest).map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten)
          = eraseFaults (shorCouplingSlot p0.1 p0.2) ++
            eraseFaults ((rest.map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten) := by
        simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
      rw [hcirc, QHL.Target.propagateCircuit_append]
      have hq0c0 : p0.1.qubit ≠ p0.2 :=
        hqc p0 (List.mem_cons_self ..) p0 (List.mem_cons_self ..)
      set es1 := propagateCircuit (eraseFaults (shorCouplingSlot p0.1 p0.2)) es with hes1
      have hndc0 : (p0.2 :: rest.map (·.2)).Nodup := hndc
      have hndq0 : (p0.1.qubit :: rest.map (·.1.qubit)).Nodup := hndq
      rcases List.mem_cons.mp hpc with rfl | hpc'
      · -- the head pair: its hook is set by the head slot, later slots keep off
        have hres : es1.paulis pc.1.qubit = couplingHook pc.1.kind (es.paulis pc.2) :=
          shorCouplingSlot_hook pc.1 pc.2 hq0c0 es _ rfl
            (hclean pc (List.mem_cons_self ..))
        rw [shorCouplings_paulis_off rest pc.1.qubit ?_ es1, hres]
        intro pc' hpc'
        constructor
        · intro h
          exact (List.nodup_cons.mp hndq0).1
            (h ▸ List.mem_map_of_mem (f := (·.1.qubit)) hpc')
        · exact hqc pc (List.mem_cons_self ..) pc' (List.mem_cons.mpr (Or.inr hpc'))
      · -- a later pair: the head slot keeps off it, then the IH applies
        have hq_ne_q0 : pc.1.qubit ≠ p0.1.qubit := by
          intro h
          exact (List.nodup_cons.mp hndq0).1
            (h ▸ List.mem_map_of_mem (f := (·.1.qubit)) hpc')
        have hq_ne_c0 : pc.1.qubit ≠ p0.2 :=
          hqc pc (List.mem_cons.mpr (Or.inr hpc')) p0 (List.mem_cons_self ..)
        have hc_ne_q0 : p0.1.qubit ≠ pc.2 :=
          hqc p0 (List.mem_cons_self ..) pc (List.mem_cons.mpr (Or.inr hpc'))
        have hc_ne_c0 : pc.2 ≠ p0.2 := by
          intro h
          exact (List.nodup_cons.mp hndc0).1
            (h ▸ List.mem_map_of_mem (f := (·.2)) hpc')
        have hcat1 : es1.paulis pc.2 = es.paulis pc.2 :=
          shorCouplingSlot_paulis_off p0.1 p0.2 pc.2 (Ne.symm hc_ne_q0) hc_ne_c0 es
        have hclean1 : ∀ pc' ∈ rest, es1.paulis pc'.1.qubit = Pauli.I := by
          intro pc'' hpc''
          have h1 : pc''.1.qubit ≠ p0.1.qubit := by
            intro h
            exact (List.nodup_cons.mp hndq0).1
              (h ▸ List.mem_map_of_mem (f := (·.1.qubit)) hpc'')
          have h2 : pc''.1.qubit ≠ p0.2 :=
            hqc pc'' (List.mem_cons.mpr (Or.inr hpc'')) p0 (List.mem_cons_self ..)
          rw [hes1, shorCouplingSlot_paulis_off p0.1 p0.2 _ h1 h2 es]
          exact hclean pc'' (List.mem_cons.mpr (Or.inr hpc''))
        have hqc' : ∀ a ∈ rest, ∀ b ∈ rest, a.1.qubit ≠ b.2 := fun a ha b hb =>
          hqc a (List.mem_cons.mpr (Or.inr ha)) b (List.mem_cons.mpr (Or.inr hb))
        rw [ih es1 (List.nodup_cons.mp hndc0).2 (List.nodup_cons.mp hndq0).2 hqc'
          hclean1 pc hpc', hcat1]

/-! ## Cascade-site zPart-vector lemmas

`couplingHook` factors through `zPart`, so the coupling walk only consumes the
Z-part of the cat vector — the `X`-junk a cascade fault spreads forward never
needs to be characterized. -/

theorem couplingHook_eq_of_zPart {k : XZPauli} {w w' : Pauli}
    (h : zPart w = zPart w') : couplingHook k w = couplingHook k w' := by
  cases k <;> simp [couplingHook, h]

/-- `zPart` of an `xPart` is always trivial. -/
theorem zPart_xPart (p : Pauli) : zPart (xPart p) = Pauli.I := by
  cases p <;> rfl

/-- `xPart` of a `zPart` is always trivial. -/
theorem xPart_zPart (p : Pauli) : xPart (zPart p) = Pauli.I := by
  cases p <;> rfl

/-- Multiplying by an `xPart` on the left never changes the `zPart`. -/
theorem zPart_pauliMul_xPart_left (a b : Pauli) :
    zPart (pauliMul (xPart a) b) = zPart b := by
  cases a <;> cases b <;> rfl

/-- Multiplying by a trivial `zPart` on the left is the identity. -/
theorem pauliMul_zPart_I {b c : Pauli} (h : zPart b = Pauli.I) :
    pauliMul (zPart b) c = c := by
  rw [h]; cases c <;> rfl

/-- One compiled cnot with a Z-free **target** changes no qubit's `zPart`:
the control commutes through (`pauliMul I`), the target only picks up an
`xPart`. -/
theorem cnot_zPart_step {nq : Nat} (c t : Fin nq) (es : ErrorState nq)
    (ht : zPart (es.paulis t) = Pauli.I) (x : Fin nq) :
    zPart ((propagateCircuit (eraseFaults (cnot c t)) es).paulis x)
      = zPart (es.paulis x) := by
  by_cases hct : c = t
  · simp [cnot, hct, propagateCircuit]
  · have he : eraseFaults (cnot c t) = [Gate.cnot c t hct] := by
      simp [cnot, hct, eraseFaults]
    rw [he]
    simp only [propagateCircuit]
    by_cases hxt : x = t
    · rw [hxt, propagateGate_cnot_target, zPart_pauliMul_xPart_left]
    · by_cases hxc : x = c
      · rw [hxc, propagateGate_cnot_control, pauliMul_zPart_I ht]
      · rw [propagateGate_cnot_paulis_ne c t hct es x hxc hxt]

/-- **Cascade pass-through (zPart projection)**: a cascade suffix whose
**targets** are all Z-free on entry changes no qubit's `zPart` (Z on a control
commutes forward; targets only accumulate `xPart`s, so they stay Z-free). -/
theorem cascade_zPart_invariant {nq : Nat} :
    ∀ (ps : List (Fin nq × Fin nq)) (es : ErrorState nq),
      (∀ p ∈ ps, zPart (es.paulis p.2) = Pauli.I) →
      ∀ x : Fin nq,
        zPart ((propagateCircuit (eraseFaults
            ((ps.map (fun cc => cnot cc.1 cc.2)).flatten)) es).paulis x)
          = zPart (es.paulis x) := by
  intro ps
  induction ps with
  | nil => intro es _ x; rfl
  | cons p0 rest ih =>
      intro es htgt x
      have hcirc : eraseFaults (((p0 :: rest).map (fun cc => cnot cc.1 cc.2)).flatten)
          = eraseFaults (cnot p0.1 p0.2) ++
            eraseFaults ((rest.map (fun cc => cnot cc.1 cc.2)).flatten) := by
        simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
      rw [hcirc, QHL.Target.propagateCircuit_append]
      set es1 := propagateCircuit (eraseFaults (cnot p0.1 p0.2)) es with hes1
      have hstep : ∀ y : Fin nq, zPart (es1.paulis y) = zPart (es.paulis y) := fun y =>
        cnot_zPart_step p0.1 p0.2 es (htgt p0 (List.mem_cons_self ..)) y
      have htgt1 : ∀ p ∈ rest, zPart (es1.paulis p.2) = Pauli.I := fun p hp =>
        (hstep p.2).trans (htgt p (List.mem_cons.mpr (Or.inr hp)))
      exact (ih es1 htgt1 x).trans (hstep x)

/-- **Verifier legs preserve every zPart off the verifier**: `cnot v c` with
any control state multiplies only `xPart (paulis v)` onto `c`, and `zPart ∘
xPart = I`; `prepP`/`hadamard`/`measZ` on `v` don't touch other qubits. -/
theorem verifierLegs_zPart_off {nq : Nat} (v c0 clast : Fin nq)
    (es : ErrorState nq) (x : Fin nq) (hx : x ≠ v) :
    zPart ((propagateCircuit (eraseFaults (prepP v ++ cnot v c0 ++ cnot v clast ++
        hadamard v ++ flagMeasZ v)) es).paulis x)
      = zPart (es.paulis x) := by
  have hprepP : eraseFaults (prepP v) = [Gate.prepPlus v] := by simp [prepP, eraseFaults]
  have hhad : eraseFaults (hadamard v) = [Gate.hadamard v] := by simp [hadamard, eraseFaults]
  have hflag : eraseFaults (flagMeasZ v) = [Gate.measZ v] := by simp [flagMeasZ, eraseFaults]
  simp only [eraseFaults_append, QHL.Target.propagateCircuit_append]
  rw [hprepP, hhad, hflag]
  simp only [propagateCircuit]
  rw [propagateGate_measZ_paulis, propagateGate_hadamard_paulis_ne _ _ _ hx]
  -- the two verifier cnots: target picks up only an xPart, control-off qubits fixed
  have hcnot_z : ∀ (t : Fin nq) (es' : ErrorState nq),
      zPart ((propagateCircuit (eraseFaults (cnot v t)) es').paulis x)
        = zPart (es'.paulis x) := by
    intro t es'
    by_cases hvt : v = t
    · simp [cnot, hvt, propagateCircuit]
    · have he : eraseFaults (cnot v t) = [Gate.cnot v t hvt] := by
        simp [cnot, hvt, eraseFaults]
      rw [he]
      simp only [propagateCircuit]
      by_cases hxt : x = t
      · rw [hxt, propagateGate_cnot_target, zPart_pauliMul_xPart_left]
      · rw [propagateGate_cnot_paulis_ne v t hvt es' x hx hxt]
  rw [hcnot_z clast _, hcnot_z c0 _,
    propagateGate_prepPlus_paulis_ne v es x hx]

/-! ## Part 3a: the uniform hook-residual core

The classifier's right branch never needs to know *which* subset of the
support carries the hook — so every pre-coupling fault site reduces to one
uniform lemma: from any coupling-entry state with clean data (and clean above
the gadget ceiling, for the conditional tail), the couplings + raw
measurements + tail produce exactly the hook-form residual, with the hook set
read off the entry state's cat Z-parts. -/

/-- `couplingHook` at a cat whose Z-part is `Z` is the schedule kind's Pauli. -/
theorem couplingHook_toPauli (k : XZPauli) (w : Pauli) (h : zPart w = Pauli.Z) :
    couplingHook k w = k.toPauli := by
  cases k <;> cases w <;> simp_all [couplingHook, zPart, hadamardAction, XZPauli.toPauli]

/-- `couplingHook` at a Z-free cat is trivial. -/
theorem couplingHook_I (k : XZPauli) (w : Pauli) (h : zPart w = Pauli.I) :
    couplingHook k w = Pauli.I := by
  cases k <;> cases w <;> simp_all [couplingHook, zPart, hadamardAction]

theorem cab_cons {nq L : Nat} {g : Gate nq} {c : Circuit nq}
    (hg : ∀ q : Fin nq, gateActsOn g q → q.val < L) (hc : circuitActsBelow c L) :
    circuitActsBelow (g :: c) L := by
  intro g' hg' q hq
  rcases List.mem_cons.mp hg' with rfl | h
  · exact hg q hq
  · exact hc g' h q hq

/-- Gates of an erased cnot-pair chain act only on pair components. -/
theorem cnotPairs_gates_actOn {nq : Nat} (ps : List (Fin nq × Fin nq)) (g : Gate nq)
    (hg : g ∈ eraseFaults ((ps.map (fun cc => cnot cc.1 cc.2)).flatten)) :
    ∀ q : Fin nq, gateActsOn g q → ∃ p ∈ ps, q = p.1 ∨ q = p.2 := by
  intro q hq
  rw [eraseFaults_flatten, List.map_map, List.mem_flatten] at hg
  obtain ⟨c, hc, hgc⟩ := hg
  rw [List.mem_map] at hc
  obtain ⟨pc, hpc, rfl⟩ := hc
  simp only [Function.comp_apply] at hgc
  by_cases hct : pc.1 = pc.2
  · simp [cnot, hct] at hgc
  · have he : eraseFaults (cnot pc.1 pc.2) = [Gate.cnot pc.1 pc.2 hct] := by
      simp [cnot, hct, eraseFaults]
    rw [he, List.mem_singleton] at hgc
    subst hgc
    rcases hq with rfl | rfl
    · exact ⟨pc, hpc, Or.inl rfl⟩
    · exact ⟨pc, hpc, Or.inr rfl⟩

/-- **Pre-coupling entry**: propagating any circuit that acts only on helper
qubits (`≥ P.n`) and below the ceiling `L`, from a clean state injected at a
qubit below the ceiling, lands at a coupling-entry state with clean data and
`cleanAbove L`. -/
theorem preCoupling_to_entry {P : QECParams} {total : Nat} (X : Circuit (P.n + total))
    (hX_above : ∀ g ∈ X, ∀ q : Fin (P.n + total), gateActsOn g q → P.n ≤ q.val)
    (L : Nat) (hX_cab : circuitActsBelow X L)
    (q0 : Fin (P.n + total)) (hq0 : q0.val < L) (hq0n : P.n ≤ q0.val)
    (p : Pauli) (dstart : Nat) :
    (∀ q' : Fin P.n,
      (propagateCircuit X ((PCC.cleanAtDetector dstart).inject q0 p)).paulis
          (freshDataQ P.n total q') = Pauli.I) ∧
    cleanAbove (propagateCircuit X ((PCC.cleanAtDetector dstart).inject q0 p)) L := by
  constructor
  · intro q'
    rw [propagateCircuit_paulis_off X (freshDataQ P.n total q') ?_ _]
    · rw [injectClean_paulis, if_neg ?_]
      intro he
      have hlt := q'.isLt
      rw [← he] at hq0n
      simp only [freshDataQ_val] at hq0n
      omega
    · intro g hg hact
      have := hX_above g hg _ hact
      have hlt := q'.isLt
      simp only [freshDataQ_val] at this
      omega
  · apply cleanAbove_preserved_of_actsBelow _ _ hX_cab
    intro h hh
    rw [injectClean_paulis, if_neg (fun he => by rw [he] at hh; omega)]

/-- **The uniform hook-residual core.**  From a coupling-entry state with
clean data and `cleanAbove L`, the couplings + raw measurements + (data-
preserving-above-`L`) tail produce exactly the subset-hook residual: the
schedule kind's Pauli on the data qubits whose cat entered with a `Z`-part,
identity elsewhere. -/
theorem shor_hook_tail_residual {P : QECParams} {total : Nat}
    (pairs : List (ScheduledPauli (P.n + total) × Fin (P.n + total)))
    (kk : XZPauli) (hkindp : ∀ pc ∈ pairs, pc.1.kind = kk)
    (hndc : (pairs.map (·.2)).Nodup) (hndq : (pairs.map (·.1.qubit)).Nodup)
    (hqvals : ∀ pc ∈ pairs, pc.1.qubit.val < P.n)
    (hcvals : ∀ pc ∈ pairs, P.n ≤ pc.2.val)
    (L : Nat) (hcatsL : ∀ pc ∈ pairs, pc.2.val < L) (hqL : P.n ≤ L)
    (measCats : List (Fin (P.n + total))) (hmeasL : ∀ c ∈ measCats, c.val < L)
    (tail : FCircuit (P.n + total))
    (htail : PreservesDataAbove (eraseFaults tail) L)
    (es1 : ErrorState (P.n + total))
    (hclean : cleanAbove es1 L)
    (hdata : ∀ q' : Fin P.n, es1.paulis (freshDataQ P.n total q') = Pauli.I)
    (q' : Fin P.n) :
    (propagateCircuit
      (eraseFaults ((pairs.map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten)
        ++ (eraseFaults ((measCats.map rawMeasZ).flatten) ++ eraseFaults tail)) es1).paulis
      (freshDataQ P.n total q')
    = if freshDataQ P.n total q'
          ∈ (pairs.filter (fun pc => zPart (es1.paulis pc.2) == Pauli.Z)).map (·.1.qubit)
      then kk.toPauli else Pauli.I := by
  have hcabC : circuitActsBelow
      (eraseFaults ((pairs.map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten)) L := by
    apply cab_erase_flatten_map
    intro pc hpc
    exact cab_erase_shorCouplingSlot pc.1 pc.2 (hcatsL pc hpc)
      (lt_of_lt_of_le (hqvals pc hpc) hqL)
  have hcabM : circuitActsBelow (eraseFaults ((measCats.map rawMeasZ).flatten)) L := by
    apply cab_erase_flatten_map
    intro c hc
    exact cab_erase_rawMeasZ c (hmeasL c hc)
  rw [QHL.Target.propagateCircuit_append, QHL.Target.propagateCircuit_append]
  set es2 := propagateCircuit
    (eraseFaults ((pairs.map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten)) es1 with hes2
  set es3 := propagateCircuit (eraseFaults ((measCats.map rawMeasZ).flatten)) es2 with hes3
  have hclean3 : cleanAbove es3 L := by
    rw [hes3, hes2]
    exact cleanAbove_preserved_of_actsBelow _ _ hcabM _
      (cleanAbove_preserved_of_actsBelow _ _ hcabC _ hclean)
  have htail3 : (propagateCircuit (eraseFaults tail) es3).paulis (freshDataQ P.n total q')
      = es3.paulis (freshDataQ P.n total q') :=
    htail es3 hclean3 (freshDataQ P.n total q') (by simp [freshDataQ_val, q'.isLt])
  rw [htail3, hes3, rawMeasZ_flatten_paulis]
  by_cases hin : freshDataQ P.n total q' ∈ pairs.map (·.1.qubit)
  · rw [List.mem_map] at hin
    obtain ⟨pc, hpc, hq⟩ := hin
    have hqc : ∀ a ∈ pairs, ∀ b ∈ pairs, a.1.qubit ≠ b.2 := by
      intro a ha b hb he
      have h1 := hqvals a ha
      have h2 := hcvals b hb
      rw [he] at h1
      omega
    have hqclean : ∀ a ∈ pairs, es1.paulis a.1.qubit = Pauli.I := by
      intro a ha
      have h1 := hqvals a ha
      have heq : a.1.qubit = freshDataQ P.n total ⟨a.1.qubit.val, h1⟩ := by
        apply Fin.ext; simp [freshDataQ_val]
      rw [heq]
      exact hdata _
    have hres := shorCouplings_from_catvec pairs es1 hndc hndq hqc hqclean pc hpc
    rw [hes2, ← hq, hres, hkindp pc hpc]
    by_cases hz : zPart (es1.paulis pc.2) = Pauli.Z
    · rw [couplingHook_toPauli kk _ hz, if_pos ?_]
      rw [List.mem_map]
      refine ⟨pc, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨hpc, by simp [hz]⟩
    · have hzI : zPart (es1.paulis pc.2) = Pauli.I := by
        cases hw : es1.paulis pc.2 <;>
          first
            | rfl
            | exact absurd (by rw [hw]; rfl) hz
      rw [couplingHook_I kk _ hzI, if_neg ?_]
      intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨pc', hpc', hq'⟩ := hmem
      rw [List.mem_filter] at hpc'
      have hpceq : pc' = pc := by
        apply List.inj_on_of_nodup_map hndq hpc'.1 hpc
        rw [hq', hq]
      rw [hpceq] at hpc'
      have := hpc'.2
      simp [hzI] at this
  · have hoff : ∀ a ∈ pairs,
        freshDataQ P.n total q' ≠ a.1.qubit ∧ freshDataQ P.n total q' ≠ a.2 := by
      intro a ha
      constructor
      · intro he
        exact hin (List.mem_map.mpr ⟨a, ha, he.symm⟩)
      · intro he
        have h2 := hcvals a ha
        have hlt := q'.isLt
        rw [← he] at h2
        simp only [freshDataQ_val] at h2
        omega
    rw [hes2, shorCouplings_paulis_off pairs _ hoff es1, hdata q', if_neg ?_]
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨pc', hpc', hq'⟩ := hmem
    rw [List.mem_filter] at hpc'
    exact hin (List.mem_map.mpr ⟨pc', hpc'.1, hq'⟩)

/--
info: 'QStab.QClifford.Compile.shorCouplings_paulis_off' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms shorCouplings_paulis_off

/--
info: 'QStab.QClifford.Compile.shorCouplings_from_catvec' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms shorCouplings_from_catvec

end QStab.QClifford.Compile
