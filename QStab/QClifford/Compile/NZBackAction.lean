import QStab.QClifford.Compile.HoarePreservation

/-!
# Generic NZ-scheme back-action characterization (reusable ∀ QEC code)

This file is deliberately **code-agnostic**: it proves a property of the *NZ
syndrome-extraction scheme's compilation*, over an arbitrary `RuleSchedule`, so
every QEC code reuses it.  (Companion files will give the Knill / Shor / Flag
characterizations in the same shape.)

The NZ gadget is `prepP(a); CX(a,q₁);…;CX(a,q_w); H(a); measZ(a)` (X-kind) or
`prep0(a); CX(q₁,a);…;CX(q_w,a); measZ(a)` (Z-kind).  A single Pauli fault on
the ancilla after the j-th CNOT propagates the gadget's CSS kind onto the
**schedule suffix** `support.drop j`.  Hence every Type-II back-action residual
of the compiled NZ gadget is one of the schedule's *suffix hooks* — the object a
concrete code then matches against its own `backActionSet`.

The proof is a genuine fault-propagation argument through the CX-chain (no
axiom, no `decide`); it is the reusable half of the surface-NZ `G1` obligation.
-/

namespace QStab.QClifford.Compile

open QStab.QClifford

/-- The CSS kind (as a `Pauli`) carried by a uniform NZ schedule. -/
def scheduleKind {n : Nat} (sigma : RuleSchedule n) : Pauli :=
  match sigma.slots.head? with
  | some slot => slot.kind.toPauli
  | none => Pauli.I

/-- The `j`-th NZ **suffix hook** of a schedule: the gadget's CSS kind on every
data qubit scheduled at position `≥ j`, identity elsewhere.  This is the
code-agnostic shape of an NZ back-action residual; `mkSurfaceHookErrors` is the
surface instance of exactly this notion (over `kindOrderRC`). -/
def nzSuffixResidual {n : Nat} (sigma : RuleSchedule n) (j : Nat) : ErrorVec n :=
  fun q =>
    if (sigma.slots.drop j).any (fun slot => decide (slot.qubit = q))
    then scheduleKind sigma
    else Pauli.I

/-- **CNOT-chain propagation** (reusable core, also the heart of the Knill / Shor
/ Flag characterizations): injecting `X` on the control `a` and propagating the
compiled CNOT chain to distinct targets `qs` (none equal `a`, initially clean on
`qs`) keeps `X` on `a` and puts `X` on every target — each step a bare
`pauliMul`, nothing behind `decide`. -/
theorem propagate_nzCnotChain_ancX {nq : Nat} (a : Fin nq) :
    ∀ qs : List (Fin nq), a ∉ qs → qs.Nodup →
      ∀ es : ErrorState nq, es.paulis a = Pauli.X → (∀ q ∈ qs, es.paulis q = Pauli.I) →
        ∀ i : Fin nq,
          (propagateCircuit (eraseFaults ((qs.map (fun q => cnot a q)).flatten)) es).paulis i =
            if i = a then Pauli.X else if i ∈ qs then Pauli.X else es.paulis i := by
  intro qs
  induction qs with
  | nil =>
      intro _ _ es hA _ i
      simp only [List.map_nil, List.flatten_nil, eraseFaults, propagateCircuit,
        List.not_mem_nil, if_false]
      by_cases h : i = a <;> simp [h, hA]
  | cons q qs' ih =>
      intro hnotin hnd es hA hQ i
      have haq : a ≠ q := by rintro rfl; exact hnotin (List.mem_cons.mpr (Or.inl rfl))
      have hnotin' : a ∉ qs' := fun h => hnotin (List.mem_cons.mpr (Or.inr h))
      have hnd' : qs'.Nodup := (List.nodup_cons.mp hnd).2
      have hqfresh : q ∉ qs' := (List.nodup_cons.mp hnd).1
      have hqmem : q ∈ q :: qs' := List.mem_cons.mpr (Or.inl rfl)
      have hcirc :
          eraseFaults (((q :: qs').map (fun q => cnot a q)).flatten) =
            Gate.cnot a q haq :: eraseFaults ((qs'.map (fun q => cnot a q)).flatten) := by
        simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
        rw [show cnot a q = [.errLoc a, .errLoc q, .gate (Gate.cnot a q haq)] from by
          simp [cnot, haq]]
        simp [eraseFaults]
      rw [hcirc, propagateCircuit]
      set es1 := propagateGate (Gate.cnot a q haq) es with hes1
      have hqI : es.paulis q = Pauli.I := hQ q hqmem
      have hes1A : es1.paulis a = Pauli.X := by
        simp [hes1, propagateGate, haq, hqI, hA, xPart, zPart, pauliMul]
      have hes1q : es1.paulis q = Pauli.X := by
        simp [hes1, propagateGate, hqI, hA, xPart, zPart, pauliMul]
      have hes1Q : ∀ q'' ∈ qs', es1.paulis q'' = Pauli.I := by
        intro q'' hq''
        have h1 : q'' ≠ a := fun h => hnotin' (h ▸ hq'')
        have h2 : q'' ≠ q := fun h => hqfresh (h ▸ hq'')
        simp [hes1, propagateGate, h1, h2, hQ q'' (List.mem_cons.mpr (Or.inr hq''))]
      rw [ih hnotin' hnd' es1 hes1A hes1Q i]
      by_cases hia : i = a
      · simp [hia]
      · rw [if_neg hia, if_neg hia]
        by_cases hiq' : i ∈ qs'
        · rw [if_pos hiq', if_pos (List.mem_cons.mpr (Or.inr hiq'))]
        · rw [if_neg hiq']
          by_cases hiq : i = q
          · subst hiq
            rw [if_pos hqmem, hes1q]
          · rw [if_neg (by simp [hiq, hiq'])]
            simp [hes1, propagateGate, hia, hiq]

/-- **CNOT-chain propagation, ancilla-target** — the direction used by the
program-path NZ gadget `compileStandardOrdered` (its Z-slots emit `cnot q anc`
with control = data `q`, target = ancilla `anc`).  Injecting Pauli `w` on the
ancilla *target* and propagating the chain leaves `w` on the ancilla and puts its
`Z`-component `zPart w` on every data control — so `X` leaves data clean while
`Y`/`Z` both deposit `Z`.  Each step a bare `pauliMul`, nothing behind `decide`. -/
theorem propagate_nzCnotChain_anc {nq : Nat} (anc : Fin nq) (w : Pauli) :
    ∀ qs : List (Fin nq), anc ∉ qs → qs.Nodup →
      ∀ es : ErrorState nq, es.paulis anc = w → (∀ q ∈ qs, es.paulis q = Pauli.I) →
        ∀ i : Fin nq,
          (propagateCircuit (eraseFaults ((qs.map (fun q => cnot q anc)).flatten)) es).paulis i =
            if i = anc then w else if i ∈ qs then zPart w else es.paulis i := by
  intro qs
  induction qs with
  | nil =>
      intro _ _ es hA _ i
      simp only [List.map_nil, List.flatten_nil, eraseFaults, propagateCircuit,
        List.not_mem_nil, if_false]
      by_cases h : i = anc <;> simp [h, hA]
  | cons q qs' ih =>
      intro hnotin hnd es hA hQ i
      have haq : anc ≠ q := by rintro rfl; exact hnotin (List.mem_cons.mpr (Or.inl rfl))
      have hqa : q ≠ anc := fun h => haq h.symm
      have hnotin' : anc ∉ qs' := fun h => hnotin (List.mem_cons.mpr (Or.inr h))
      have hnd' : qs'.Nodup := (List.nodup_cons.mp hnd).2
      have hqfresh : q ∉ qs' := (List.nodup_cons.mp hnd).1
      have hqmem : q ∈ q :: qs' := List.mem_cons.mpr (Or.inl rfl)
      have hcirc :
          eraseFaults (((q :: qs').map (fun q => cnot q anc)).flatten) =
            Gate.cnot q anc hqa :: eraseFaults ((qs'.map (fun q => cnot q anc)).flatten) := by
        simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
        rw [show cnot q anc = [.errLoc q, .errLoc anc, .gate (Gate.cnot q anc hqa)] from by
          simp [cnot, hqa]]
        simp [eraseFaults]
      rw [hcirc, propagateCircuit]
      set es1 := propagateGate (Gate.cnot q anc hqa) es with hes1
      have hqI : es.paulis q = Pauli.I := hQ q hqmem
      have hes1A : es1.paulis anc = w := by
        simp [hes1, propagateGate, hqI, hA, xPart]
      have hes1q : es1.paulis q = zPart w := by
        simp [hes1, propagateGate, hqa, hqI, hA]
      have hes1Q : ∀ q'' ∈ qs', es1.paulis q'' = Pauli.I := by
        intro q'' hq''
        have h1 : q'' ≠ anc := fun h => hnotin' (h ▸ hq'')
        have h2 : q'' ≠ q := fun h => hqfresh (h ▸ hq'')
        simp [hes1, propagateGate, h1, h2, hQ q'' (List.mem_cons.mpr (Or.inr hq''))]
      rw [ih hnotin' hnd' es1 hes1A hes1Q i]
      by_cases hia : i = anc
      · simp [hia]
      · rw [if_neg hia, if_neg hia]
        by_cases hiq' : i ∈ qs'
        · rw [if_pos hiq', if_pos (List.mem_cons.mpr (Or.inr hiq'))]
        · rw [if_neg hiq']
          by_cases hiq : i = q
          · subst hiq
            rw [if_pos hqmem, hes1q]
          · rw [if_neg (by simp [hiq, hiq'])]
            simp [hes1, propagateGate, hia, hiq]

/-! ### Gate-locality: a gate not acting on qubit `d` leaves `es.paulis d` fixed
(reusable glue for the per-site residual walk + tail invariance). -/

theorem propagateGate_cnot_paulis_ne {nq : Nat} (c t : Fin nq) (h : c ≠ t)
    (es : ErrorState nq) (d : Fin nq) (hc : d ≠ c) (ht : d ≠ t) :
    (propagateGate (Gate.cnot c t h) es).paulis d = es.paulis d := by
  simp [propagateGate, ht, hc]

theorem propagateGate_hadamard_paulis_ne {nq : Nat} (a : Fin nq) (es : ErrorState nq)
    (d : Fin nq) (h : d ≠ a) :
    (propagateGate (Gate.hadamard a) es).paulis d = es.paulis d := by
  simp [propagateGate, h]

theorem propagateGate_prepZero_paulis_ne {nq : Nat} (a : Fin nq) (es : ErrorState nq)
    (d : Fin nq) (h : d ≠ a) :
    (propagateGate (Gate.prepZero a) es).paulis d = es.paulis d := by
  simp [propagateGate, h]

theorem propagateGate_prepPlus_paulis_ne {nq : Nat} (a : Fin nq) (es : ErrorState nq)
    (d : Fin nq) (h : d ≠ a) :
    (propagateGate (Gate.prepPlus a) es).paulis d = es.paulis d := by
  simp [propagateGate, h]

/-- `propagateGate (hadamard a)` at the acted qubit. -/
theorem propagateGate_hadamard_self {nq : Nat} (a : Fin nq) (es : ErrorState nq) :
    (propagateGate (Gate.hadamard a) es).paulis a = hadamardAction (es.paulis a) := by
  show (if a = a then hadamardAction (es.paulis a) else es.paulis a) = hadamardAction (es.paulis a)
  rw [if_pos rfl]

/-- `propagateGate (cnot c t)` at the control `c`. -/
theorem propagateGate_cnot_control {nq : Nat} (c t : Fin nq) (h : c ≠ t) (es : ErrorState nq) :
    (propagateGate (Gate.cnot c t h) es).paulis c =
      pauliMul (zPart (es.paulis t)) (es.paulis c) := by
  show (if c = t then pauliMul (xPart (es.paulis c)) (es.paulis t)
        else if c = c then pauliMul (zPart (es.paulis t)) (es.paulis c) else es.paulis c) =
      pauliMul (zPart (es.paulis t)) (es.paulis c)
  rw [if_neg h, if_pos rfl]

/-- `propagateGate (cnot c t)` at the target `t`. -/
theorem propagateGate_cnot_target {nq : Nat} (c t : Fin nq) (h : c ≠ t) (es : ErrorState nq) :
    (propagateGate (Gate.cnot c t h) es).paulis t =
      pauliMul (xPart (es.paulis c)) (es.paulis t) := by
  show (if t = t then pauliMul (xPart (es.paulis c)) (es.paulis t) else _) =
      pauliMul (xPart (es.paulis c)) (es.paulis t)
  rw [if_pos rfl]

/-- Multiplying a Z-free Pauli by an `X`-component stays Z-free. -/
theorem zPart_pauliMul_xPart {a b : Pauli} (hb : zPart b = Pauli.I) :
    zPart (pauliMul (xPart a) b) = Pauli.I := by
  cases a <;> cases b <;> simp_all [xPart, zPart, pauliMul]

/-- **X-slot H-sandwich preserves the data control.**  The X-kind `zParitySlot`
compiles to `H q ; cnot q anc ; H q`; when the ancilla is *Z-free*, this leaves the
data qubit `q`'s Pauli exactly fixed (it only dumps `X` onto the ancilla).  This is
the fact that makes a data residual survive later X-stabilizer gadgets unchanged
(tail invariance). -/
theorem propagate_hSandwich_preserves_control {nq : Nat} (q anc : Fin nq) (h : q ≠ anc)
    (es : ErrorState nq) (hanc : zPart (es.paulis anc) = Pauli.I) :
    (propagateCircuit (eraseFaults (hadamard q ++ cnot q anc ++ hadamard q)) es).paulis q =
      es.paulis q := by
  have hcirc : eraseFaults (hadamard q ++ cnot q anc ++ hadamard q) =
      [Gate.hadamard q, Gate.cnot q anc h, Gate.hadamard q] := by
    simp [hadamard, cnot, h, eraseFaults]
  rw [hcirc]
  simp only [propagateCircuit]
  set es1 := propagateGate (Gate.hadamard q) es with he1
  have he1anc : zPart (es1.paulis anc) = Pauli.I := by
    rw [he1, propagateGate_hadamard_paulis_ne q es anc (Ne.symm h)]; exact hanc
  have he1q : es1.paulis q = hadamardAction (es.paulis q) := by
    rw [he1, propagateGate_hadamard_self]
  set es2 := propagateGate (Gate.cnot q anc h) es1 with he2
  have he2q : es2.paulis q = hadamardAction (es.paulis q) := by
    rw [he2, propagateGate_cnot_control q anc h, he1anc, he1q]; simp [pauliMul]
  rw [propagateGate_hadamard_self, he2q]
  cases es.paulis q <;> simp [hadamardAction]

/-- The X-slot H-sandwich keeps the ancilla Z-free (it only ever accumulates `X`). -/
theorem propagate_hSandwich_keeps_ancZfree {nq : Nat} (q anc : Fin nq) (h : q ≠ anc)
    (es : ErrorState nq) (hanc : zPart (es.paulis anc) = Pauli.I) :
    zPart ((propagateCircuit (eraseFaults (hadamard q ++ cnot q anc ++ hadamard q)) es).paulis anc) =
      Pauli.I := by
  have hcirc : eraseFaults (hadamard q ++ cnot q anc ++ hadamard q) =
      [Gate.hadamard q, Gate.cnot q anc h, Gate.hadamard q] := by
    simp [hadamard, cnot, h, eraseFaults]
  rw [hcirc]
  simp only [propagateCircuit]
  set es1 := propagateGate (Gate.hadamard q) es with he1
  have he1anc : es1.paulis anc = es.paulis anc := by
    rw [he1, propagateGate_hadamard_paulis_ne q es anc (Ne.symm h)]
  set es2 := propagateGate (Gate.cnot q anc h) es1 with he2
  rw [propagateGate_hadamard_paulis_ne q es2 anc (Ne.symm h), he2,
    propagateGate_cnot_target q anc h, he1anc]
  exact zPart_pauliMul_xPart hanc

/-- A control is left fixed by `cnot` when the target carries no `Z`-component. -/
theorem propagateGate_cnot_control_preserved {nq : Nat} (c t : Fin nq) (h : c ≠ t)
    (es : ErrorState nq) (ht : zPart (es.paulis t) = Pauli.I) :
    (propagateGate (Gate.cnot c t h) es).paulis c = es.paulis c := by
  rw [propagateGate_cnot_control, ht]; rfl

/-- **Z-slot chain preserves data** (the core of NZ tail-invariance): propagating a
Z-parity chain `[cnot q₁ anc, …, cnot qₘ anc]` leaves every qubit `d ≠ anc` fixed,
provided the ancilla starts Z-free — data qubits are controls, and the ancilla only
ever accumulates `X`. -/
theorem propagate_zChain_preserves_data {nq : Nat} (anc : Fin nq) :
    ∀ qs : List (Fin nq), anc ∉ qs →
      ∀ es : ErrorState nq, zPart (es.paulis anc) = Pauli.I →
        ∀ d : Fin nq, d ≠ anc →
          (propagateCircuit (eraseFaults ((qs.map (fun q => cnot q anc)).flatten)) es).paulis d =
            es.paulis d := by
  intro qs
  induction qs with
  | nil => intro _ es _ d _; simp [propagateCircuit]
  | cons q qs' ih =>
      intro hnotin es hancZ d hd
      have hqa : q ≠ anc := by rintro rfl; exact hnotin (List.mem_cons.mpr (Or.inl rfl))
      have hnotin' : anc ∉ qs' := fun hh => hnotin (List.mem_cons.mpr (Or.inr hh))
      have hcirc :
          eraseFaults (((q :: qs').map (fun q => cnot q anc)).flatten) =
            Gate.cnot q anc hqa :: eraseFaults ((qs'.map (fun q => cnot q anc)).flatten) := by
        simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
        rw [show cnot q anc = [.errLoc q, .errLoc anc, .gate (Gate.cnot q anc hqa)] from by
          simp [cnot, hqa]]
        simp [eraseFaults]
      rw [hcirc, propagateCircuit]
      set es1 := propagateGate (Gate.cnot q anc hqa) es with he1
      have he1ancZ : zPart (es1.paulis anc) = Pauli.I := by
        rw [he1, propagateGate_cnot_target]
        exact zPart_pauliMul_xPart hancZ
      have he1d : es1.paulis d = es.paulis d := by
        by_cases hdq : d = q
        · rw [hdq, he1, propagateGate_cnot_control_preserved q anc hqa es hancZ]
        · rw [he1, propagateGate_cnot_paulis_ne q anc hqa es d hdq hd]
      rw [ih hnotin' es1 he1ancZ d hd, he1d]

/-- A single `zParitySlot` keeps the ancilla Z-free (both kinds: Z dumps `X` on the
target; X's H-sandwich also only dumps `X`). -/
theorem zParitySlot_keeps_ancZfree {nq : Nat} (anc : Fin nq) (slot : ScheduledPauli nq)
    (hqa : slot.qubit ≠ anc) (es : ErrorState nq) (hanc : zPart (es.paulis anc) = Pauli.I) :
    zPart ((propagateCircuit (eraseFaults (zParitySlot anc slot)) es).paulis anc) = Pauli.I := by
  obtain ⟨sk, sq⟩ := slot
  cases sk with
  | X => exact propagate_hSandwich_keeps_ancZfree sq anc hqa es hanc
  | Z =>
      have hc : eraseFaults (zParitySlot anc ⟨.Z, sq⟩) = [Gate.cnot sq anc hqa] := by
        simp [zParitySlot, cnot, hqa, eraseFaults]
      rw [hc]
      simp only [propagateCircuit]
      rw [propagateGate_cnot_target sq anc hqa]
      exact zPart_pauliMul_xPart hanc

/-- A single `zParitySlot` preserves every data qubit `d ≠ anc` when the ancilla is
Z-free (Z via control-commute, X via the H-sandwich). -/
theorem zParitySlot_preserves_data {nq : Nat} (anc : Fin nq) (slot : ScheduledPauli nq)
    (hqa : slot.qubit ≠ anc) (es : ErrorState nq) (hanc : zPart (es.paulis anc) = Pauli.I)
    (d : Fin nq) (hd : d ≠ anc) :
    (propagateCircuit (eraseFaults (zParitySlot anc slot)) es).paulis d = es.paulis d := by
  obtain ⟨sk, sq⟩ := slot
  cases sk with
  | X =>
      by_cases hdq : d = sq
      · rw [hdq]; exact propagate_hSandwich_preserves_control sq anc hqa es hanc
      · have hc : eraseFaults (zParitySlot anc ⟨.X, sq⟩) =
            [Gate.hadamard sq, Gate.cnot sq anc hqa, Gate.hadamard sq] := by
          simp [zParitySlot, hadamard, cnot, hqa, eraseFaults]
        rw [hc]
        simp only [propagateCircuit]
        rw [propagateGate_hadamard_paulis_ne sq _ d hdq,
          propagateGate_cnot_paulis_ne sq anc hqa _ d hdq hd,
          propagateGate_hadamard_paulis_ne sq es d hdq]
  | Z =>
      have hc : eraseFaults (zParitySlot anc ⟨.Z, sq⟩) = [Gate.cnot sq anc hqa] := by
        simp [zParitySlot, cnot, hqa, eraseFaults]
      rw [hc]
      simp only [propagateCircuit]
      by_cases hdq : d = sq
      · rw [hdq]; exact propagateGate_cnot_control_preserved sq anc hqa es hanc
      · exact propagateGate_cnot_paulis_ne sq anc hqa es d hdq hd

/-- **Full `zParitySlots` chain preserves data** (mixed X/Z schedule): induction over
the slots, threading the ancilla-Z-free invariant through each `zParitySlot`. -/
theorem zParitySlots_preserves_data {nq : Nat} (anc : Fin nq) :
    ∀ slots : List (ScheduledPauli nq), (∀ s ∈ slots, s.qubit ≠ anc) →
      ∀ es : ErrorState nq, zPart (es.paulis anc) = Pauli.I →
        ∀ d : Fin nq, d ≠ anc →
          (propagateCircuit (eraseFaults ((slots.map (zParitySlot anc)).flatten)) es).paulis d =
            es.paulis d := by
  intro slots
  induction slots with
  | nil => intro _ es _ d _; simp [propagateCircuit]
  | cons s rest ih =>
      intro hq es hancZ d hd
      have hsq : s.qubit ≠ anc := hq s (List.mem_cons.mpr (Or.inl rfl))
      have hrest : ∀ s' ∈ rest, s'.qubit ≠ anc := fun s' h => hq s' (List.mem_cons.mpr (Or.inr h))
      have hcirc : eraseFaults (((s :: rest).map (zParitySlot anc)).flatten) =
          eraseFaults (zParitySlot anc s) ++
            eraseFaults ((rest.map (zParitySlot anc)).flatten) := by
        simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
      rw [hcirc, QHL.Target.propagateCircuit_append]
      have he1ancZ :
          zPart ((propagateCircuit (eraseFaults (zParitySlot anc s)) es).paulis anc) = Pauli.I :=
        zParitySlot_keeps_ancZfree anc s hsq es hancZ
      have he1d :
          (propagateCircuit (eraseFaults (zParitySlot anc s)) es).paulis d = es.paulis d :=
        zParitySlot_preserves_data anc s hsq es hancZ d hd
      rw [ih hrest _ he1ancZ d hd, he1d]

/-- `prepZero` resets its qubit to the identity Pauli. -/
theorem propagateGate_prepZero_self {nq : Nat} (q : Fin nq) (es : ErrorState nq) :
    (propagateGate (Gate.prepZero q) es).paulis q = Pauli.I := by
  show (if q = q then Pauli.I else es.paulis q) = Pauli.I
  rw [if_pos rfl]

/-- `measZ` leaves every Pauli unchanged (it only records a measurement outcome). -/
theorem propagateGate_measZ_paulis {nq : Nat} (q d : Fin nq) (es : ErrorState nq) :
    (propagateGate (Gate.measZ q) es).paulis d = es.paulis d := rfl

/-- **Full NZ gadget preserves data**: `compileStandardOrdered` leaves every data
qubit `d ≠ anc` fixed — `prep0` makes the ancilla Z-free, the parity chain preserves
data, and `flagMeasZ` touches no Pauli. -/
theorem compileStandardOrdered_preserves_data {nq : Nat} (sigma : RuleSchedule nq) (anc : Fin nq)
    (hq : ∀ s ∈ sigma.slots, s.qubit ≠ anc) (es : ErrorState nq) (d : Fin nq) (hd : d ≠ anc) :
    (propagateCircuit (eraseFaults (compileStandardOrdered sigma anc)) es).paulis d =
      es.paulis d := by
  have h1 : compileStandardOrdered sigma anc =
      prep0 anc ++ (sigma.slots.map (zParitySlot anc)).flatten ++ flagMeasZ anc := rfl
  have hprep : eraseFaults (prep0 anc) = [Gate.prepZero anc] := by simp [prep0, eraseFaults]
  have hmeas : eraseFaults (flagMeasZ anc) = [Gate.measZ anc] := by simp [flagMeasZ, eraseFaults]
  rw [h1, eraseFaults_append, eraseFaults_append, hprep, hmeas,
    QHL.Target.propagateCircuit_append, QHL.Target.propagateCircuit_append]
  simp only [propagateCircuit]
  rw [propagateGate_measZ_paulis]
  set esA := propagateGate (Gate.prepZero anc) es with hA
  have hAanc : zPart (esA.paulis anc) = Pauli.I := by
    simp [hA, propagateGate_prepZero_self, zPart]
  have hAd : esA.paulis d = es.paulis d := by
    rw [hA]; exact propagateGate_prepZero_paulis_ne anc es d hd
  rw [zParitySlots_preserves_data anc sigma.slots hq esA hAanc d hd, hAd]

/-- A program uses only the NZ syndrome-extraction scheme. -/
def XZProgram.allNZ {n : Nat} : XZProgram n → Prop
  | .skip => True
  | .meas scheme _ => scheme = Scheme.NZ
  | .seq a b => XZProgram.allNZ a ∧ XZProgram.allNZ b

/-- **Program-level NZ tail-invariance**: an all-NZ compiled program preserves every
data qubit `d` (`d.val < n`).  Each gadget's ancilla is a helper (`.val = n+start ≥ n`),
so it is distinct from every (lifted, `< n`) data qubit; the gadget lemma then applies
and the seq case is a straightforward append induction. -/
theorem compileProgramAux_preserves_data {n total : Nat} :
    ∀ (start : Nat) (program : XZProgram n)
      (hfit : start + programHelperCount program ≤ total), XZProgram.allNZ program →
      ∀ (es : ErrorState (n + total)) (d : Fin (n + total)), d.val < n →
        (propagateCircuit (eraseFaults (compileProgramAux start program hfit)) es).paulis d =
          es.paulis d := by
  intro start program
  induction program generalizing start with
  | skip => intro hfit _ es d _; simp [compileProgramAux, propagateCircuit]
  | meas scheme sigma =>
      intro hfit hnz es d hd
      simp only [XZProgram.allNZ] at hnz
      subst hnz
      have ha : (blockHelperQ n total start 1 hfit ⟨0, by decide⟩).val = n + start := by
        simp [blockHelperQ]
      have hda : d ≠ blockHelperQ n total start 1 hfit ⟨0, by decide⟩ := by
        intro h; rw [h, ha] at hd; omega
      have hslot : ∀ s ∈ (liftSchedule sigma).slots,
          s.qubit ≠ blockHelperQ n total start 1 hfit ⟨0, by decide⟩ := by
        intro s hs h
        simp only [liftSchedule, List.mem_map] at hs
        obtain ⟨s', _, hseq⟩ := hs
        have hval : s.qubit.val = n + start := by rw [h, ha]
        rw [← hseq] at hval
        simp only [liftSlot, freshDataQ_val] at hval
        have := s'.qubit.isLt
        omega
      exact compileStandardOrdered_preserves_data (liftSchedule sigma)
        (blockHelperQ n total start 1 hfit ⟨0, by decide⟩) hslot es d hda
  | seq first second ihf ihs =>
      intro hfit hnz es d hd
      obtain ⟨hnzf, hnzs⟩ := hnz
      simp only [compileProgramAux, eraseFaults_append, QHL.Target.propagateCircuit_append]
      rw [ihs _ _ hnzs _ d hd, ihf _ _ hnzf es d hd]

/-- A single gate preserves the all-identity Pauli state (the vacuum). -/
theorem propagateGate_preserves_allI {nq : Nat} (g : Gate nq) (es : ErrorState nq)
    (h : ∀ i, es.paulis i = Pauli.I) (d : Fin nq) :
    (propagateGate g es).paulis d = Pauli.I := by
  cases g <;> simp [propagateGate, h, pauliMul, xPart, zPart, hadamardAction]

/-- **Vacuum preservation**: propagating any circuit through the all-identity state
leaves it all-identity.  Used to show `prep0` faults are filtered — `prepZero` wipes
the injected ancilla error, and the residual then propagates as the vacuum. -/
theorem propagateCircuit_preserves_allI {nq : Nat} (C : Circuit nq) :
    ∀ (es : ErrorState nq), (∀ i, es.paulis i = Pauli.I) →
      ∀ d, (propagateCircuit C es).paulis d = Pauli.I := by
  induction C with
  | nil => intro es h d; simpa [propagateCircuit] using h d
  | cons g rest ih =>
      intro es h d
      simp only [propagateCircuit]
      exact ih (propagateGate g es) (fun i => propagateGate_preserves_allI g es h i) d

/-- **Inverse walk reduction**: every event produced by the reverse back-action walk
comes from an `errLoc` site of the circuit (in `prefixErrLocsWithContextAux`) with some
nontrivial injected Pauli.  This turns the walk into a site-enumeration problem. -/
theorem walk_event_from_prefix_site {P : QECParams} {total : Nat}
    (readout : ErrorState (P.n + total) → Bool) :
    ∀ (cursor : Nat) (fc tail : FCircuit (P.n + total)) (event : CompiledBackActionEvent P),
      event ∈ reverseCurrentBackActionEventsAux readout cursor fc tail →
        ∃ (site : PCC.ErrLocWithContext (P.n + total)) (p : Pauli) (hp : p ≠ Pauli.I),
          site ∈ prefixErrLocsWithContextAux cursor fc tail ∧
            compiledBackActionEventOfFault readout ⟨site, p, hp⟩ = event ∧
              ErrorVec.weight event.residual ≠ 0 ∧ ErrorVec.weight event.residual ≠ 1 := by
  intro cursor fc
  induction fc generalizing cursor with
  | nil =>
      intro tail event h
      exact h.elim
  | cons instr rest ih =>
      cases instr with
      | gate g =>
          intro tail event h
          obtain ⟨site, p, hp, hsite, heq, hw0, hw1⟩ :=
            ih (cursor + PCC.gateDetectorAdvance g) tail event h
          refine ⟨site, p, hp, ?_, heq, hw0, hw1⟩
          simpa only [prefixErrLocsWithContextAux] using hsite
      | errLoc q0 =>
          intro tail event h
          have h2 :
              event ∈ reverseCurrentBackActionEventsAux readout cursor rest tail ∨
                ∃ (p : Pauli) (hp : p ≠ Pauli.I),
                  compiledBackActionEventOfFault readout
                      ⟨⟨q0, eraseFaults rest ++ eraseFaults tail, cursor⟩, p, hp⟩ = event ∧
                    ErrorVec.weight event.residual ≠ 0 ∧ ErrorVec.weight event.residual ≠ 1 := h
          rcases h2 with hrec | ⟨p, hp, hfault, hw0, hw1⟩
          · obtain ⟨site, p', hp', hsite, heq, hw0, hw1⟩ := ih cursor tail event hrec
            refine ⟨site, p', hp', ?_, heq, hw0, hw1⟩
            simp only [prefixErrLocsWithContextAux]
            exact List.mem_cons.mpr (Or.inr hsite)
          · refine ⟨⟨q0, eraseFaults rest ++ eraseFaults tail, cursor⟩, p, hp, ?_, hfault, hw0, hw1⟩
            simp only [prefixErrLocsWithContextAux]
            exact List.mem_cons.mpr (Or.inl rfl)

/-- **Site-level append decomposition**: the `errLoc` sites of `c1 ++ c2` split into
those of `c1` (with `c2` folded into their continuation) and those of `c2` (at the
advanced cursor).  Lets the gadget be peeled into `prep0` / slots / `flagMeasZ`. -/
theorem prefixErrLocs_append {nq : Nat} (c1 : FCircuit nq) :
    ∀ (cursor : Nat) (c2 tail : FCircuit nq),
      prefixErrLocsWithContextAux cursor (c1 ++ c2) tail =
        prefixErrLocsWithContextAux cursor c1 (c2 ++ tail) ++
          prefixErrLocsWithContextAux (cursor + fCircuitDetectorAdvance c1) c2 tail := by
  induction c1 with
  | nil => intro cursor c2 tail; simp [prefixErrLocsWithContextAux, fCircuitDetectorAdvance]
  | cons instr rest ih =>
      cases instr with
      | gate g =>
          intro cursor c2 tail
          simp only [List.cons_append, prefixErrLocsWithContextAux, fCircuitDetectorAdvance,
            ih (cursor + PCC.gateDetectorAdvance g), Nat.add_assoc]
      | errLoc q0 =>
          intro cursor c2 tail
          simp only [List.cons_append, prefixErrLocsWithContextAux, fCircuitDetectorAdvance,
            eraseFaults_append, List.append_assoc, List.cons_append, ih cursor]

/-- A `prepZero` on the injected qubit wipes the injected error: the state becomes
the vacuum.  (Boundary case: `prep0` faults are filtered.) -/
theorem injectClean_prepZero_allI {nq : Nat} (a : Fin nq) (p : Pauli) (dstart : Nat) (i : Fin nq) :
    (propagateGate (Gate.prepZero a) ((PCC.cleanAtDetector dstart).inject a p)).paulis i = Pauli.I := by
  by_cases h : i = a <;>
    simp [propagateGate, ErrorState.inject, PCC.cleanAtDetector, ErrorState.clean, h]

/-- A `measZ` on the injected ancilla leaves every other qubit (in particular data)
identity.  (Boundary case: `flagMeasZ` faults are filtered.) -/
theorem injectClean_measZ_data_I {nq : Nat} (a : Fin nq) (p : Pauli) (dstart : Nat)
    (d : Fin nq) (hd : d ≠ a) :
    (propagateGate (Gate.measZ a) ((PCC.cleanAtDetector dstart).inject a p)).paulis d = Pauli.I := by
  rw [propagateGate_measZ_paulis]
  simp [ErrorState.inject, PCC.cleanAtDetector, ErrorState.clean, hd]

/-- An all-identity error vector has weight `0`. -/
theorem weight_zero_of_allI {n : Nat} (e : ErrorVec n) (h : ∀ i, e i = Pauli.I) :
    ErrorVec.weight e = 0 := by
  simp only [ErrorVec.weight, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  simp [h i]

/-- An error vector supported on (at most) a single qubit has weight `≤ 1`. -/
theorem weight_le_one_of_single {n : Nat} (e : ErrorVec n) (q0 : Fin n)
    (h : ∀ i, i ≠ q0 → e i = Pauli.I) : ErrorVec.weight e ≤ 1 := by
  have hsub : (Finset.univ.filter fun i => e i ≠ Pauli.I) ⊆ {q0} := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [Finset.mem_singleton]
    by_contra hne
    exact hi (h i hne)
  have hcard := Finset.card_le_card hsub
  simpa [ErrorVec.weight, Finset.card_singleton] using hcard

/-- The Pauli field of a clean-then-inject state: `p` on the injected qubit, `I`
elsewhere.  A reusable computation rule for fault residuals. -/
theorem injectClean_paulis {nq : Nat} (q0 : Fin nq) (p : Pauli) (dstart : Nat) (i : Fin nq) :
    ((PCC.cleanAtDetector dstart).inject q0 p).paulis i = if i = q0 then p else Pauli.I := by
  have hc : (PCC.cleanAtDetector dstart).paulis i = Pauli.I := rfl
  show (if i = q0 then pauliMul p ((PCC.cleanAtDetector dstart).paulis i)
        else (PCC.cleanAtDetector dstart).paulis i) = if i = q0 then p else Pauli.I
  rw [hc]
  by_cases h : i = q0
  · rw [if_pos h, if_pos h]; cases p <;> rfl
  · rw [if_neg h, if_neg h]

/-- **H-sandwich chain propagation** (the X-slot dual of `propagate_nzCnotChain_anc`):
injecting Pauli `w` on the ancilla and propagating the X-slot chain
`H q ; cnot q anc ; H q` leaves `w` on the ancilla and puts `hadamardAction (zPart w)`
on every data qubit — so `X` leaves data clean while `Y`/`Z` deposit `X`. -/
theorem propagate_nzHSandwichChain_anc {nq : Nat} (anc : Fin nq) (w : Pauli) :
    ∀ qs : List (Fin nq), anc ∉ qs → qs.Nodup →
      ∀ es : ErrorState nq, es.paulis anc = w → (∀ q ∈ qs, es.paulis q = Pauli.I) →
        ∀ i : Fin nq,
          (propagateCircuit (eraseFaults
              ((qs.map (fun q => hadamard q ++ cnot q anc ++ hadamard q)).flatten)) es).paulis i =
            if i = anc then w else if i ∈ qs then hadamardAction (zPart w) else es.paulis i := by
  intro qs
  induction qs with
  | nil =>
      intro _ _ es hA _ i
      simp only [List.map_nil, List.flatten_nil, eraseFaults, propagateCircuit,
        List.not_mem_nil, if_false]
      by_cases h : i = anc <;> simp [h, hA]
  | cons q qs' ih =>
      intro hnotin hnd es hA hQ i
      have haq : anc ≠ q := by rintro rfl; exact hnotin (List.mem_cons.mpr (Or.inl rfl))
      have hqa : q ≠ anc := fun h => haq h.symm
      have hnotin' : anc ∉ qs' := fun h => hnotin (List.mem_cons.mpr (Or.inr h))
      have hnd' : qs'.Nodup := (List.nodup_cons.mp hnd).2
      have hqfresh : q ∉ qs' := (List.nodup_cons.mp hnd).1
      have hqmem : q ∈ q :: qs' := List.mem_cons.mpr (Or.inl rfl)
      have hqI : es.paulis q = Pauli.I := hQ q hqmem
      have hcirc :
          eraseFaults (((q :: qs').map (fun q => hadamard q ++ cnot q anc ++ hadamard q)).flatten) =
            [Gate.hadamard q, Gate.cnot q anc hqa, Gate.hadamard q] ++
              eraseFaults ((qs'.map (fun q => hadamard q ++ cnot q anc ++ hadamard q)).flatten) := by
        simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
        congr 1
        simp [hadamard, cnot, hqa, eraseFaults]
      rw [hcirc, QHL.Target.propagateCircuit_append]
      set es1 := propagateCircuit [Gate.hadamard q, Gate.cnot q anc hqa, Gate.hadamard q] es with hes1
      have hHq : (propagateGate (Gate.hadamard q) es).paulis q = Pauli.I := by
        simp [propagateGate_hadamard_self, hqI, hadamardAction]
      have hHa : (propagateGate (Gate.hadamard q) es).paulis anc = w := by
        rw [propagateGate_hadamard_paulis_ne q es anc (Ne.symm hqa), hA]
      have hes1A : es1.paulis anc = w := by
        rw [hes1]; simp only [propagateCircuit]
        rw [propagateGate_hadamard_paulis_ne q _ anc (Ne.symm hqa),
          propagateGate_cnot_target q anc hqa, hHq, hHa]
        simp [xPart, pauliMul]
      have hes1q : es1.paulis q = hadamardAction (zPart w) := by
        rw [hes1]; simp only [propagateCircuit]
        rw [propagateGate_hadamard_self, propagateGate_cnot_control q anc hqa, hHq, hHa]
        simp [pauliMul_I_right]
      have hes1Q : ∀ q'' ∈ qs', es1.paulis q'' = Pauli.I := by
        intro q'' hq''
        have h1 : q'' ≠ anc := fun h => hnotin' (h ▸ hq'')
        have h2 : q'' ≠ q := fun h => hqfresh (h ▸ hq'')
        rw [hes1]; simp only [propagateCircuit]
        rw [propagateGate_hadamard_paulis_ne q _ q'' h2,
          propagateGate_cnot_paulis_ne q anc hqa _ q'' h2 h1,
          propagateGate_hadamard_paulis_ne q es q'' h2,
          hQ q'' (List.mem_cons.mpr (Or.inr hq''))]
      rw [ih hnotin' hnd' es1 hes1A hes1Q i]
      by_cases hia : i = anc
      · simp [hia]
      · rw [if_neg hia, if_neg hia]
        by_cases hiq' : i ∈ qs'
        · rw [if_pos hiq', if_pos (List.mem_cons.mpr (Or.inr hiq'))]
        · rw [if_neg hiq']
          by_cases hiq : i = q
          · subst hiq
            rw [if_pos hqmem, hes1q]
          · rw [if_neg (by simp [hiq, hiq'])]
            rw [hes1]; simp only [propagateCircuit]
            rw [propagateGate_hadamard_paulis_ne q _ i hiq,
              propagateGate_cnot_paulis_ne q anc hqa _ i hiq hia,
              propagateGate_hadamard_paulis_ne q es i hiq]

/-- **Ancilla-Z chain residual on data** (the surviving chain case): injecting `Z`
on the ancilla and propagating the Z-parity chain leaves `Z` on exactly the chain's
data qubits — i.e. the schedule suffix hook. -/
theorem residual_anc_chain_data {P : QECParams} {total : Nat} (anc : Fin (P.n + total))
    (qs : List (Fin (P.n + total))) (hanc : anc ∉ qs) (hnd : qs.Nodup)
    (hancHelper : P.n ≤ anc.val) (dstart : Nat) (p : Pauli) (q' : Fin P.n) :
    (propagateCircuit (eraseFaults ((qs.map (fun q => cnot q anc)).flatten))
        ((PCC.cleanAtDetector dstart).inject anc p)).paulis (freshDataQ P.n total q') =
      if freshDataQ P.n total q' ∈ qs then zPart p else Pauli.I := by
  have hesA : ((PCC.cleanAtDetector dstart).inject anc p).paulis anc = p := by
    rw [injectClean_paulis, if_pos rfl]
  have hesQ : ∀ q ∈ qs, ((PCC.cleanAtDetector dstart).inject anc p).paulis q = Pauli.I := by
    intro q hq
    have hqa : q ≠ anc := fun h => hanc (h ▸ hq)
    rw [injectClean_paulis, if_neg hqa]
  have hne : freshDataQ P.n total q' ≠ anc :=
    Fin.ne_of_val_ne (by have := q'.isLt; simp only [freshDataQ_val]; omega)
  have hfreshI :
      ((PCC.cleanAtDetector dstart).inject anc p).paulis (freshDataQ P.n total q') = Pauli.I := by
    rw [injectClean_paulis, if_neg hne]
  rw [propagate_nzCnotChain_anc anc p qs hanc hnd _ hesA hesQ (freshDataQ P.n total q'),
    if_neg hne, hfreshI]

/-- Ancilla residual through an H-sandwich (X-slot) chain: the X-slot dual of
`residual_anc_chain_data`, depositing `hadamardAction (zPart p)` on the suffix. -/
theorem residual_anc_Hchain_data {P : QECParams} {total : Nat} (anc : Fin (P.n + total))
    (qs : List (Fin (P.n + total))) (hanc : anc ∉ qs) (hnd : qs.Nodup)
    (hancHelper : P.n ≤ anc.val) (dstart : Nat) (p : Pauli) (q' : Fin P.n) :
    (propagateCircuit (eraseFaults
        ((qs.map (fun q => hadamard q ++ cnot q anc ++ hadamard q)).flatten))
        ((PCC.cleanAtDetector dstart).inject anc p)).paulis (freshDataQ P.n total q') =
      if freshDataQ P.n total q' ∈ qs then hadamardAction (zPart p) else Pauli.I := by
  have hesA : ((PCC.cleanAtDetector dstart).inject anc p).paulis anc = p := by
    rw [injectClean_paulis, if_pos rfl]
  have hesQ : ∀ q ∈ qs, ((PCC.cleanAtDetector dstart).inject anc p).paulis q = Pauli.I := by
    intro q hq
    have hqa : q ≠ anc := fun h => hanc (h ▸ hq)
    rw [injectClean_paulis, if_neg hqa]
  have hne : freshDataQ P.n total q' ≠ anc :=
    Fin.ne_of_val_ne (by have := q'.isLt; simp only [freshDataQ_val]; omega)
  have hfreshI :
      ((PCC.cleanAtDetector dstart).inject anc p).paulis (freshDataQ P.n total q') = Pauli.I := by
    rw [injectClean_paulis, if_neg hne]
  rw [propagate_nzHSandwichChain_anc anc p qs hanc hnd _ hesA hesQ (freshDataQ P.n total q'),
    if_neg hne, hfreshI]

/-- Ancilla H-sandwich residual with a trailing data-preserving tail. -/
theorem residual_anc_HchainTail {P : QECParams} {total : Nat} (a : Fin (P.n + total))
    (qs : List (Fin (P.n + total))) (hanc : a ∉ qs) (hnd : qs.Nodup) (hancHelper : P.n ≤ a.val)
    (tailGates : Circuit (P.n + total))
    (htail : ∀ (es : ErrorState (P.n + total)) (q'' : Fin P.n),
      (propagateCircuit tailGates es).paulis (freshDataQ P.n total q'') =
        es.paulis (freshDataQ P.n total q''))
    (dstart : Nat) (p : Pauli) (q' : Fin P.n) :
    (propagateCircuit (eraseFaults
        ((qs.map (fun q => hadamard q ++ cnot q a ++ hadamard q)).flatten) ++ tailGates)
        ((PCC.cleanAtDetector dstart).inject a p)).paulis (freshDataQ P.n total q') =
      if freshDataQ P.n total q' ∈ qs then hadamardAction (zPart p) else Pauli.I := by
  rw [QHL.Target.propagateCircuit_append, htail]
  exact residual_anc_Hchain_data a qs hanc hnd hancHelper dstart p q'

/-- Ancilla site residual through a Z-parity chain followed by a data-preserving tail
(e.g. the gadget's `measZ`): the injected Pauli's `Z`-component on the schedule suffix. -/
theorem residual_anc_chainTail {P : QECParams} {total : Nat} (a : Fin (P.n + total))
    (qs : List (Fin (P.n + total))) (hanc : a ∉ qs) (hnd : qs.Nodup) (hancHelper : P.n ≤ a.val)
    (tailGates : Circuit (P.n + total))
    (htail : ∀ (es : ErrorState (P.n + total)) (q'' : Fin P.n),
      (propagateCircuit tailGates es).paulis (freshDataQ P.n total q'') =
        es.paulis (freshDataQ P.n total q''))
    (dstart : Nat) (p : Pauli) (q' : Fin P.n) :
    (propagateCircuit (eraseFaults ((qs.map (fun q => cnot q a)).flatten) ++ tailGates)
        ((PCC.cleanAtDetector dstart).inject a p)).paulis (freshDataQ P.n total q') =
      if freshDataQ P.n total q' ∈ qs then zPart p else Pauli.I := by
  rw [QHL.Target.propagateCircuit_append, htail]
  exact residual_anc_chain_data a qs hanc hnd hancHelper dstart p q'

/-- Data-qubit site residual through the chain + data-preserving tail: the fault stays
on the injected data qubit alone (hence weight ≤ 1). -/
theorem residual_data_chainTail {P : QECParams} {total : Nat} (a : Fin (P.n + total))
    (qs : List (Fin (P.n + total))) (hanc : a ∉ qs) (hancHelper : P.n ≤ a.val)
    (tailGates : Circuit (P.n + total))
    (htail : ∀ (es : ErrorState (P.n + total)) (q'' : Fin P.n),
      (propagateCircuit tailGates es).paulis (freshDataQ P.n total q'') =
        es.paulis (freshDataQ P.n total q''))
    (dstart : Nat) (q0 : Fin (P.n + total)) (hq0 : q0 ∈ qs) (p : Pauli) (q' : Fin P.n) :
    (propagateCircuit (eraseFaults ((qs.map (fun q => cnot q a)).flatten) ++ tailGates)
        ((PCC.cleanAtDetector dstart).inject q0 p)).paulis (freshDataQ P.n total q') =
      if freshDataQ P.n total q' = q0 then p else Pauli.I := by
  rw [QHL.Target.propagateCircuit_append, htail]
  have haq0 : a ≠ q0 := fun h => hanc (h ▸ hq0)
  have hancZ : zPart (((PCC.cleanAtDetector dstart).inject q0 p).paulis a) = Pauli.I := by
    simp [injectClean_paulis, haq0]
  have hane : freshDataQ P.n total q' ≠ a :=
    Fin.ne_of_val_ne (by have := q'.isLt; simp only [freshDataQ_val]; omega)
  rw [propagate_zChain_preserves_data a qs hanc _ hancZ (freshDataQ P.n total q') hane,
    injectClean_paulis]

/-- The two `errLoc` sites of a compiled `cnot q a`: the data control `q` and the
ancilla `a`, both sharing the suffix `cnot q a :: eraseFaults tail` (both errLocs sit
before the gate). -/
theorem prefixErrLocs_cnot {nq : Nat} (a q : Fin nq) (hqa : q ≠ a) (cursor : Nat)
    (tail : FCircuit nq) :
    prefixErrLocsWithContextAux cursor (cnot q a) tail =
      [⟨q, Gate.cnot q a hqa :: eraseFaults tail, cursor⟩,
       ⟨a, Gate.cnot q a hqa :: eraseFaults tail, cursor⟩] := by
  have hc : cnot q a = [FInstr.errLoc q, FInstr.errLoc a, FInstr.gate (Gate.cnot q a hqa)] := by
    simp [cnot, hqa]
  rw [hc]
  simp [prefixErrLocsWithContextAux, eraseFaults]

/-- eraseFaults of a Z-parity chain, peeling the head cnot. -/
theorem eraseFaults_cnotChain_cons {nq : Nat} (a q : Fin nq) (hqa : q ≠ a)
    (qs' : List (Fin nq)) :
    eraseFaults (((q :: qs').map (fun q => cnot q a)).flatten) =
      Gate.cnot q a hqa :: eraseFaults ((qs'.map (fun q => cnot q a)).flatten) := by
  simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
  rw [show cnot q a = [FInstr.errLoc q, FInstr.errLoc a, FInstr.gate (Gate.cnot q a hqa)] from by
    simp [cnot, hqa]]
  simp [eraseFaults]

/-- **Z-gadget chain characterization**: every fault site of the compiled Z-parity
chain `(qs.map (cnot · a)).flatten` (followed by a data-preserving tail) whose data
residual survives the weight filter (`≠ 0, ≠ 1`) produces the `Z` suffix hook on some
`qs.drop k`.  Data-qubit faults give weight ≤ 1; ancilla-`X` gives weight 0; only
ancilla-`Y`/`Z` survive, depositing `Z` on the whole current suffix. -/
theorem chain_residual_hook {P : QECParams} {total : Nat} (a : Fin (P.n + total))
    (hancHelper : P.n ≤ a.val) (tail : FCircuit (P.n + total))
    (htail : ∀ (es : ErrorState (P.n + total)) (q'' : Fin P.n),
      (propagateCircuit (eraseFaults tail) es).paulis (freshDataQ P.n total q'') =
        es.paulis (freshDataQ P.n total q'')) :
    ∀ (qs : List (Fin (P.n + total))), (∀ q ∈ qs, q.val < P.n) → qs.Nodup →
      ∀ (cursor : Nat) (site : PCC.ErrLocWithContext (P.n + total)) (p : Pauli) (hp : p ≠ Pauli.I),
        site ∈ prefixErrLocsWithContextAux cursor ((qs.map (fun q => cnot q a)).flatten) tail →
        ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≠ 0 →
        ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≠ 1 →
        ∃ k, targetFaultDataResidual P ⟨site, p, hp⟩ =
          fun q' => if freshDataQ P.n total q' ∈ qs.drop k then Pauli.Z else Pauli.I := by
  intro qs
  induction qs with
  | nil =>
      intro _ _ cursor site p hp hsite _ _
      simp [prefixErrLocsWithContextAux] at hsite
  | cons q qs' ih =>
      intro hlt hnd cursor site p hp hsite hw0 hw1
      have hqlt : q.val < P.n := hlt q (List.mem_cons.mpr (Or.inl rfl))
      have hqa : q ≠ a := fun h => by
        have := hlt q (List.mem_cons.mpr (Or.inl rfl)); rw [h] at this; omega
      have hlt' : ∀ q'' ∈ qs', q''.val < P.n := fun q'' h => hlt q'' (List.mem_cons.mpr (Or.inr h))
      have hnd' : qs'.Nodup := (List.nodup_cons.mp hnd).2
      have hanc : a ∉ (q :: qs') := fun h => by have := hlt a h; omega
      rw [show ((q :: qs').map (fun q => cnot q a)).flatten =
            cnot q a ++ (qs'.map (fun q => cnot q a)).flatten from by
            simp [List.map_cons, List.flatten_cons],
          prefixErrLocs_append] at hsite
      simp only [List.mem_append] at hsite
      have hsuffix :
          Gate.cnot q a hqa :: eraseFaults ((qs'.map (fun q => cnot q a)).flatten ++ tail) =
            eraseFaults (((q :: qs').map (fun q => cnot q a)).flatten) ++ eraseFaults tail := by
        rw [eraseFaults_append, eraseFaults_cnotChain_cons a q hqa, List.cons_append]
      rcases hsite with hhead | hrec
      · rw [prefixErrLocs_cnot a q hqa] at hhead
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hhead
        rcases hhead with rfl | rfl
        · -- data site: single-qubit residual, weight ≤ 1 ⇒ excluded
          exfalso
          have hres : targetFaultDataResidual P
              ⟨⟨q, Gate.cnot q a hqa :: eraseFaults ((qs'.map (fun q => cnot q a)).flatten ++ tail),
                cursor⟩, p, hp⟩ =
              fun q' => if freshDataQ P.n total q' = q then p else Pauli.I := by
            funext q'
            show (propagateCircuit
                (Gate.cnot q a hqa :: eraseFaults ((qs'.map (fun q => cnot q a)).flatten ++ tail))
                ((PCC.cleanAtDetector cursor).inject q p)).paulis (freshDataQ P.n total q') = _
            rw [hsuffix]
            exact residual_data_chainTail a (q :: qs') hanc hancHelper (eraseFaults tail) htail
              cursor q (List.mem_cons.mpr (Or.inl rfl)) p q'
          rw [hres] at hw0 hw1
          have hle : ErrorVec.weight
              (fun q' => if freshDataQ P.n total q' = q then p else Pauli.I) ≤ 1 := by
            apply weight_le_one_of_single _ ⟨q.val, hqlt⟩
            intro q'' hne
            have hfne : freshDataQ P.n total q'' ≠ q := by
              intro h
              apply hne; apply Fin.ext
              simpa [freshDataQ_val] using congrArg Fin.val h
            rw [if_neg hfne]
          omega
        · -- ancilla site: zPart p on the whole current suffix
          have hres : targetFaultDataResidual P
              ⟨⟨a, Gate.cnot q a hqa :: eraseFaults ((qs'.map (fun q => cnot q a)).flatten ++ tail),
                cursor⟩, p, hp⟩ =
              fun q' => if freshDataQ P.n total q' ∈ (q :: qs') then zPart p else Pauli.I := by
            funext q'
            show (propagateCircuit
                (Gate.cnot q a hqa :: eraseFaults ((qs'.map (fun q => cnot q a)).flatten ++ tail))
                ((PCC.cleanAtDetector cursor).inject a p)).paulis (freshDataQ P.n total q') = _
            rw [hsuffix]
            exact residual_anc_chainTail a (q :: qs') hanc hnd hancHelper (eraseFaults tail) htail
              cursor p q'
          by_cases hzp : zPart p = Pauli.I
          · exfalso
            apply hw0
            apply weight_zero_of_allI
            intro q'
            rw [hres]; simp [hzp]
          · have hzZ : zPart p = Pauli.Z := by cases p <;> simp_all [zPart]
            refine ⟨0, ?_⟩
            rw [hres]
            funext q'
            simp [hzZ, List.drop_zero]
      · obtain ⟨k, hk⟩ := ih hlt' hnd' _ site p hp hrec hw0 hw1
        exact ⟨k + 1, hk⟩

/-- Z-uniform schedule: the compiled parity chain is the plain qubit CNOT chain. -/
theorem zChain_eq {nq : Nat} (a : Fin nq) (slots : List (ScheduledPauli nq))
    (hz : ∀ s ∈ slots, s.kind = XZPauli.Z) :
    (slots.map (zParitySlot a)).flatten =
      ((slots.map (·.qubit)).map (fun q => cnot q a)).flatten := by
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro s hs
  have hks : s.kind = XZPauli.Z := hz s hs
  simp only [Function.comp_apply, zParitySlot, hks]

/-- A `prep0`-site fault: `prepZero` wipes the injected error, so the residual is
identity on every qubit (in particular all data). -/
theorem residual_prep0_site {P : QECParams} {total : Nat} (a : Fin (P.n + total)) (p : Pauli)
    (rest : Circuit (P.n + total)) (dstart : Nat) (q' : Fin P.n) :
    (propagateCircuit (Gate.prepZero a :: rest)
        ((PCC.cleanAtDetector dstart).inject a p)).paulis (freshDataQ P.n total q') = Pauli.I := by
  rw [propagateCircuit]
  exact propagateCircuit_preserves_allI rest _
    (fun i => injectClean_prepZero_allI a p dstart i) (freshDataQ P.n total q')

/-- A `measZ`-site fault (on the ancilla): residual on data is identity. -/
theorem residual_measZ_site {P : QECParams} {total : Nat} (a : Fin (P.n + total)) (p : Pauli)
    (hancHelper : P.n ≤ a.val) (dstart : Nat) (q' : Fin P.n) :
    (propagateCircuit [Gate.measZ a]
        ((PCC.cleanAtDetector dstart).inject a p)).paulis (freshDataQ P.n total q') = Pauli.I := by
  have hne : freshDataQ P.n total q' ≠ a :=
    Fin.ne_of_val_ne (by have := q'.isLt; simp only [freshDataQ_val]; omega)
  simp only [propagateCircuit, propagateGate_measZ_paulis]
  rw [injectClean_paulis, if_neg hne]

/-- `freshDataQ` is injective (it preserves `.val`). -/
theorem freshDataQ_inj {n k : Nat} {q q' : Fin n}
    (h : freshDataQ n k q = freshDataQ n k q') : q = q' := by
  apply Fin.ext
  simpa [freshDataQ_val] using congrArg Fin.val h

/-- The chain's `Z`-suffix hook over the *lifted* qubits equals the schedule's
`nzSuffixResidual` (the surface-facing form), when the schedule kind is `Z`. -/
theorem nzSuffix_of_liftedChain {P : QECParams} {total : Nat} (sigma : RuleSchedule P.n)
    (hsk : scheduleKind sigma = Pauli.Z) (k : Nat) :
    (fun q' : Fin P.n =>
        if freshDataQ P.n total q' ∈ (((sigma.slots.map liftSlot).map (·.qubit)).drop k)
        then Pauli.Z else Pauli.I) = nzSuffixResidual sigma k := by
  funext q'
  simp only [nzSuffixResidual, hsk]
  have hmem :
      (freshDataQ P.n total q' ∈ (((sigma.slots.map liftSlot).map (·.qubit)).drop k)) ↔
        ((sigma.slots.drop k).any (fun slot => decide (slot.qubit = q')) = true) := by
    rw [List.map_map, ← List.map_drop]
    simp only [List.mem_map, List.any_eq_true, Function.comp_apply, decide_eq_true_eq, liftSlot]
    constructor
    · rintro ⟨s, hs, hsq⟩
      exact ⟨s, hs, freshDataQ_inj hsq⟩
    · rintro ⟨s, hs, hsq⟩
      exact ⟨s, hs, by rw [hsq]⟩
  by_cases hc : freshDataQ P.n total q' ∈ (((sigma.slots.map liftSlot).map (·.qubit)).drop k)
  · rw [if_pos hc, if_pos (hmem.mp hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hmem.mpr h))]

/-- The single `errLoc` site of a compiled `prep0 a`. -/
theorem prefixErrLocs_prep0 {nq : Nat} (a : Fin nq) (cursor : Nat) (tail : FCircuit nq) :
    prefixErrLocsWithContextAux cursor (prep0 a) tail =
      [⟨a, Gate.prepZero a :: eraseFaults tail, cursor⟩] := by
  simp [prep0, prefixErrLocsWithContextAux, eraseFaults]

/-- The single `errLoc` site of a compiled `flagMeasZ a`. -/
theorem prefixErrLocs_flagMeasZ {nq : Nat} (a : Fin nq) (cursor : Nat) (tail : FCircuit nq) :
    prefixErrLocsWithContextAux cursor (flagMeasZ a) tail =
      [⟨a, Gate.measZ a :: eraseFaults tail, cursor⟩] := by
  simp [flagMeasZ, prefixErrLocsWithContextAux, eraseFaults]

/-- **Within-gadget NZ back-action characterization** (reusable for every QEC code):
every Type-II residual produced by faults in the compiled NZ gadget *in isolation*
(`tail = []`) is one of the schedule's suffix hooks.

NOTE (corrected 2026-07-01): the earlier form quantified over an *arbitrary* `tail`
and was too strong — `targetFaultDataResidual` propagates through the whole suffix
`rest ++ tail`, so an arbitrary tail can change the residual.  In the program
obligation (`reverseProgramBackActionResiduals`) the tail is always a *compiled NZ
program*, which preserves data residuals (H-sandwich + Z-control, with a
fresh-ancilla invariant); that **tail-invariance** is a separate lemma composed with
this within-gadget characterization. -/
theorem reverseNZ_residuals_subset_suffix {P : QECParams} {total : Nat}
    (sigma : RuleSchedule P.n) (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount .NZ sigma ≤ total)
    (hz : ∀ s ∈ sigma.slots, s.kind = XZPauli.Z)
    (hnd : (sigma.slots.map (·.qubit)).Nodup) :
    ∀ residual : ErrorVec P.n,
      residual ∈
          reverseGadgetBackActionResiduals .NZ sigma helperStart detectorStart
            helperFit ([] : FCircuit (P.n + total)) →
        ∃ j : Nat, residual = nzSuffixResidual sigma j := by
  intro residual hres
  obtain ⟨event, hev, hreq⟩ := hres
  obtain ⟨site, p, hp, hsite, heq, hw0, hw1⟩ :=
    walk_event_from_prefix_site _ detectorStart _ ([] : FCircuit (P.n + total)) event hev
  have hev_res : event.residual = targetFaultDataResidual P ⟨site, p, hp⟩ := by rw [← heq]; rfl
  rw [hev_res] at hw0 hw1
  rw [← hreq, hev_res]
  set a : Fin (P.n + total) := blockHelperQ P.n total helperStart 1 helperFit ⟨0, by decide⟩ with ha
  have hancHelper : P.n ≤ a.val := by rw [ha]; simp [blockHelperQ]
  have hgb : compileGadgetBlock .NZ sigma helperStart helperFit =
      prep0 a ++ ((liftSchedule sigma).slots.map (zParitySlot a)).flatten ++ flagMeasZ a := rfl
  rw [hgb, show prep0 a ++ ((liftSchedule sigma).slots.map (zParitySlot a)).flatten ++ flagMeasZ a =
        prep0 a ++ (((liftSchedule sigma).slots.map (zParitySlot a)).flatten ++ flagMeasZ a) from by
        rw [List.append_assoc],
      prefixErrLocs_append, prefixErrLocs_append] at hsite
  simp only [List.mem_append] at hsite
  -- data-preserving tail for the chain: the trailing measZ
  have htail : ∀ (es : ErrorState (P.n + total)) (q'' : Fin P.n),
      (propagateCircuit (eraseFaults (flagMeasZ a)) es).paulis (freshDataQ P.n total q'') =
        es.paulis (freshDataQ P.n total q'') := by
    intro es q''
    have hef : eraseFaults (flagMeasZ a) = [Gate.measZ a] := by simp [flagMeasZ, eraseFaults]
    rw [hef]; simp only [propagateCircuit, propagateGate_measZ_paulis]
  rcases hsite with hprep | hchain | hmeas
  · -- prep0 site: residual is identity ⇒ weight 0, contradiction
    rw [prefixErrLocs_prep0] at hprep
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hprep
    subst hprep
    exact absurd (weight_zero_of_allI _ (fun q' => residual_prep0_site a p _ detectorStart q')) hw0
  · -- chain site: the Z suffix hook
    rw [zChain_eq a (liftSchedule sigma).slots
        (fun s hs => by
          simp only [liftSchedule, List.mem_map] at hs
          obtain ⟨s', hs', rfl⟩ := hs
          simp [liftSlot, hz s' hs'])] at hchain
    have hqlt : ∀ q ∈ (liftSchedule (k := total) sigma).slots.map (·.qubit), q.val < P.n := by
      intro q hq
      simp only [liftSchedule, List.map_map, List.mem_map] at hq
      obtain ⟨s, _, rfl⟩ := hq
      simp [liftSlot]
    have hqnd : ((liftSchedule (k := total) sigma).slots.map (·.qubit)).Nodup := by
      have : (liftSchedule (k := total) sigma).slots.map (·.qubit) =
          (sigma.slots.map (·.qubit)).map (freshDataQ P.n total) := by
        simp [liftSchedule, List.map_map, liftSlot, Function.comp]
      rw [this]; exact hnd.map (fun _ _ => freshDataQ_inj)
    obtain ⟨k, hk⟩ := chain_residual_hook a hancHelper (flagMeasZ a) htail
      ((liftSchedule (k := total) sigma).slots.map (·.qubit)) hqlt hqnd _ site p hp hchain hw0 hw1
    have hsk : scheduleKind sigma = Pauli.Z := by
      have hne : sigma.slots ≠ [] := by
        rintro he
        simp [he, liftSchedule, prefixErrLocsWithContextAux] at hchain
      obtain ⟨s0, rest0, hs0⟩ := List.exists_cons_of_ne_nil hne
      simp only [scheduleKind, hs0, List.head?_cons, hz s0 (by rw [hs0]; simp)]
      rfl
    exact ⟨k, hk.trans (nzSuffix_of_liftedChain sigma hsk k)⟩
  · -- measZ site: residual is identity on data ⇒ weight 0, contradiction
    rw [prefixErrLocs_flagMeasZ] at hmeas
    simp only [List.mem_cons, List.not_mem_nil, or_false, eraseFaults] at hmeas
    subst hmeas
    exact absurd (weight_zero_of_allI _
      (fun q' => residual_measZ_site a p hancHelper _ q')) hw0

end QStab.QClifford.Compile
