import QStab.Paper.CodeDistance
import Mathlib.Data.Fintype.Pi

/-!
# No-go / "Dangerous" Proof-Carrying Code

A **No-go PCC** certificate carries the opposite message of a `Safe` certificate.  Where a
`Safe` certificate convinces the verifier "*every* run with `< d` faults is harmless" (and
exhibits one `d`-fault reach witness for tightness), a **Dangerous** certificate convinces the
verifier of the dual: "*there is* a run with `< d` faults that already produces an undetected
logical error — this circuit does **not** have fault-distance `d`."  Structurally a dangerous
certificate is exactly a **reach witness below the claimed distance**, so the same verifier
machinery that checks the `reach` slot checks it.

The headline instance here is a genuine **impossibility theorem**: for the perfect `[[5,1,3]]`
code, **no** stabilizer-measurement schedule under the Standard (unflagged) scheme preserves
circuit-level distance `3`.  For *every* CNOT ordering, a single ancilla fault mid-ladder
deposits a weight-2 **hook** which, together with one more single-qubit fault, is an undetected
nontrivial logical — a 2-fault attack.  The message to the verifier is: *stop trying, you will
never succeed.*  This is why flag/cat/transversal schemes exist: they catch the hook that the
Standard scheme cannot.

The core combinatorial fact (`nogo_core`) is a finite kernel `decide`; everything else is a
structural derivation.  Axiom-clean: `[propext, Classical.choice, Quot.sound]`, no `native_decide`.
-/

set_option maxRecDepth 8192

namespace QStab.Examples.FiveQubitNoGo

open QStab QStab.Paper.CodeDistance

instance : Fintype Pauli where
  elems := {Pauli.I, Pauli.X, Pauli.Y, Pauli.Z}
  complete := fun p => by cases p <;> decide

/-- Positional 5-qubit Pauli vector. -/
def v5 (a b c d e : Pauli) : ErrorVec 5 := fun q =>
  if q.val = 0 then a else if q.val = 1 then b else if q.val = 2 then c
  else if q.val = 3 then d else e

/-- The `[[5,1,3]]` stabilizer generators (cyclic `XZZXI` family), each of weight 4. -/
def fqStab : Fin 4 → ErrorVec 5
  | ⟨0, _⟩ => v5 .X .Z .Z .X .I  -- XZZXI
  | ⟨1, _⟩ => v5 .I .X .Z .Z .X  -- IXZZX
  | ⟨2, _⟩ => v5 .X .I .X .Z .Z  -- XIXZZ
  | ⟨3, _⟩ => v5 .Z .X .I .X .Z  -- ZXIXZ

/-- Logical `Z̄ = ZZZZZ` and `X̄ = XXXXX`. -/
def fqLogicalZ : ErrorVec 5 := v5 .Z .Z .Z .Z .Z
def fqLogicalX : ErrorVec 5 := v5 .X .X .X .X .X

/-- The five-qubit code as `QECParams` (combinatorial fields; `backActionSet` is irrelevant to
the no-go, which quantifies over schedules explicitly). -/
def fqParams : QECParams where
  n := 5; k := 1; d := 3; R := 1; numStab := 4
  stabilizers := fqStab
  backActionSet := fun _ => ∅
  r := 0
  backAction_weight_bound := by intro s e he; exact he.elim
  C_budget := 2
  hn := by omega
  hns := by omega
  hR := by omega

/-! ## Fault model: single-qubit faults and schedule-induced suffix hooks -/

/-- A single-qubit (Type-0) fault: Pauli `P` on qubit `q`. -/
@[reducible] def single (q : Fin 5) (P : Pauli) : ErrorVec 5 :=
  fun q' => if q' = q then P else Pauli.I

/-- The restriction of an operator to a set of positions (the physical shape of a hook: the
stabilizer's Pauli on the qubits still coupled after the fault). -/
@[reducible] def restrictTo (E : ErrorVec 5) (S : List (Fin 5)) : ErrorVec 5 :=
  fun q => if q ∈ S then E q else Pauli.I

/-- The weight-2 suffix hook of stabilizer `i` when its last two CNOT targets are `c, d`. -/
@[reducible] def suffix2 (i : Fin 4) (c d : Fin 5) : ErrorVec 5 := restrictTo (fqStab i) [c, d]

/-- An error is **undetected** if it centralizes every stabilizer generator. -/
@[reducible] def undetected (E : ErrorVec 5) : Prop :=
  ∀ j : Fin 4, ErrorVec.parity (fqStab j) E = false

/-- An error is a **nontrivial logical** if it anticommutes with `X̄` or `Z̄` (hence `∉ Stab`). -/
@[reducible] def nontrivialLogical (E : ErrorVec 5) : Prop :=
  ErrorVec.parity fqLogicalZ E = true ∨ ErrorVec.parity fqLogicalX E = true

/-- A **logical failure**: undetected and nontrivial — an error the code cannot see but that
corrupts the encoded information. -/
@[reducible] def badLogical (E : ErrorVec 5) : Prop := undetected E ∧ nontrivialLogical E

/-! ## The no-go core (finite kernel `decide`) -/

/-- **The no-go core.**  Every weight-2 restriction of every stabilizer generator — i.e. the
weight-2 suffix hook exposed by *any* CNOT ordering ending in a support pair `{c,d}` — completes,
via a single further qubit fault, to an undetected nontrivial logical.  Kernel-checked over the
finite space of `(generator, pair, completing fault)`; the combinatorial engine of the no-go. -/
theorem nogo_core :
    ∀ (i : Fin 4) (c d : Fin 5), c ≠ d → fqStab i c ≠ Pauli.I → fqStab i d ≠ Pauli.I →
      ∃ (q : Fin 5) (P : Pauli), P ≠ Pauli.I ∧
        badLogical (ErrorVec.mul (suffix2 i c d) (single q P)) := by decide

/-! ## Standard-scheme schedules -/

/-- A Standard-scheme measurement schedule: a CNOT ordering of each stabilizer's four support
qubits.  `ord i = (a,b,c,d)` couples stabilizer `i`'s data qubits to the ancilla in the order
`a,b,c,d`, then measures the ancilla.  `wf` requires each ordering to be a genuine permutation of
the generator's weight-4 support (four distinct support qubits). -/
structure StdSchedule where
  ord : Fin 4 → Fin 5 × Fin 5 × Fin 5 × Fin 5
  wf : ∀ i, [(ord i).1, (ord i).2.1, (ord i).2.2.1, (ord i).2.2.2].Nodup ∧
        fqStab i (ord i).1 ≠ Pauli.I ∧ fqStab i (ord i).2.1 ≠ Pauli.I ∧
        fqStab i (ord i).2.2.1 ≠ Pauli.I ∧ fqStab i (ord i).2.2.2 ≠ Pauli.I

/-- The ordered list of CNOT targets for stabilizer `i` under `sched`. -/
def orderList (sched : StdSchedule) (i : Fin 4) : List (Fin 5) :=
  [(sched.ord i).1, (sched.ord i).2.1, (sched.ord i).2.2.1, (sched.ord i).2.2.2]

/-- **One elementary circuit fault** under a schedule: either a single-qubit (Type-0) fault, or a
suffix hook (Type-II) — the stabilizer restricted to a nonempty suffix of its CNOT ordering, the
residual an ancilla fault mid-ladder deposits on the data. -/
def IsFault (sched : StdSchedule) (F : ErrorVec 5) : Prop :=
  (∃ q P, F = single q P) ∨
  (∃ i : Fin 4, ∃ s : List (Fin 5), s <:+ orderList sched i ∧ s ≠ [] ∧
    F = restrictTo (fqStab i) s)

/-- `ReachableBy sched t E`: the data residual `E` is a product of at most `t` elementary
faults under `sched`. -/
def ReachableBy (sched : StdSchedule) : Nat → ErrorVec 5 → Prop
  | 0, E => E = ErrorVec.identity 5
  | (t + 1), E => ReachableBy sched t E ∨
      (∃ F E', IsFault sched F ∧ ReachableBy sched t E' ∧ E = ErrorVec.mul F E')

/-! ## Dangerous / No-go PCC -/

/-- A **dangerous witness** at fault-budget `t`: an undetected nontrivial logical reachable with
at most `t` faults.  (The dual of the `reach` slot — a reach witness *below* the claimed
distance.) -/
def DangerousWitness (sched : StdSchedule) (t : Nat) : Prop :=
  ∃ E, ReachableBy sched t E ∧ badLogical E

/-- A schedule **preserves fault-distance `d`** if no undetected nontrivial logical is reachable
with fewer than `d` faults. -/
def PreservesDistance (sched : StdSchedule) (d : Nat) : Prop :=
  ∀ E, ReachableBy sched (d - 1) E → ¬ badLogical E

/-- **Dangerous-soundness** (the verifier's rule): a dangerous witness at budget `d-1` refutes
distance preservation at `d`.  This is the No-go analogue of `vcgen_sound`. -/
theorem dangerous_sound (sched : StdSchedule) (d : Nat) :
    DangerousWitness sched (d - 1) → ¬ PreservesDistance sched d := by
  rintro ⟨E, hreach, hbad⟩ hpres
  exact hpres E hreach hbad

/-! ## Auxiliary algebra -/

theorem mul_identity (E : ErrorVec 5) : ErrorVec.mul E (ErrorVec.identity 5) = E := by
  funext q
  simp only [ErrorVec.mul, ErrorVec.identity]
  cases E q <;> rfl

/-- The last two CNOT targets of stabilizer `i` are distinct support qubits. -/
theorem last2_ne (sched : StdSchedule) (i : Fin 4) :
    (sched.ord i).2.2.1 ≠ (sched.ord i).2.2.2 := by
  have h := (sched.wf i).1
  simp only [List.nodup_cons, List.mem_cons, or_false, List.mem_nil_iff] at h
  tauto

theorem last2_supp1 (sched : StdSchedule) (i : Fin 4) :
    fqStab i (sched.ord i).2.2.1 ≠ Pauli.I := (sched.wf i).2.2.2.1

theorem last2_supp2 (sched : StdSchedule) (i : Fin 4) :
    fqStab i (sched.ord i).2.2.2 ≠ Pauli.I := (sched.wf i).2.2.2.2

/-- The weight-2 suffix hook of stabilizer `i` is a genuine circuit fault under `sched`. -/
theorem suffix2_isFault (sched : StdSchedule) (i : Fin 4) :
    IsFault sched (suffix2 i (sched.ord i).2.2.1 (sched.ord i).2.2.2) := by
  right
  refine ⟨i, [(sched.ord i).2.2.1, (sched.ord i).2.2.2], ?_, ?_, rfl⟩
  · exact ⟨[(sched.ord i).1, (sched.ord i).2.1], rfl⟩
  · exact List.cons_ne_nil _ _

/-! ## The headline no-go theorem -/

/-- **No Standard schedule preserves distance 3 for the `[[5,1,3]]` code.**  For *every* CNOT
ordering there is a 2-fault undetected logical: take stabilizer `0`, its ordering's weight-2
suffix hook, and the completing single-qubit fault from `nogo_core`. -/
theorem fiveQubit_standard_dangerous (sched : StdSchedule) : DangerousWitness sched 2 := by
  obtain ⟨q, P, hP, hbad⟩ :=
    nogo_core 0 (sched.ord 0).2.2.1 (sched.ord 0).2.2.2
      (last2_ne sched 0) (last2_supp1 sched 0) (last2_supp2 sched 0)
  refine ⟨ErrorVec.mul (suffix2 0 (sched.ord 0).2.2.1 (sched.ord 0).2.2.2) (single q P), ?_, hbad⟩
  -- reachable by 2 faults: the suffix hook, then the single-qubit fault
  right
  refine ⟨suffix2 0 (sched.ord 0).2.2.1 (sched.ord 0).2.2.2, single q P,
    suffix2_isFault sched 0, ?_, rfl⟩
  -- the single-qubit fault is reachable in 1
  right
  exact ⟨single q P, ErrorVec.identity 5, Or.inl ⟨q, P, rfl⟩, rfl, (mul_identity _).symm⟩

/-- **The No-go capstone.**  No Standard-scheme schedule gives the `[[5,1,3]]` code
circuit-level fault-distance `3` — a mechanized impossibility result. -/
theorem fiveQubit_standard_nogo (sched : StdSchedule) : ¬ PreservesDistance sched 3 :=
  dangerous_sound sched 3 (fiveQubit_standard_dangerous sched)

/-! ## Rigor: the witness really is a logical error (`∉ Stab`) -/

theorem fqLogicalZ_cent : ∀ i, ErrorVec.parity fqLogicalZ (fqStab i) = false := by decide
theorem fqLogicalX_cent : ∀ i, ErrorVec.parity fqLogicalX (fqStab i) = false := by decide

/-- A `badLogical` error is genuinely outside the stabilizer group — justifying "nontrivial
logical" against the real `InStab` predicate (via the generic `parity_commutes_of_InStab`). -/
theorem badLogical_notInStab {E : ErrorVec 5} (h : badLogical E) :
    ¬ QStab.InStab fqParams E := by
  intro hStab
  have hcZ := parity_commutes_of_InStab (P := fqParams) fqLogicalZ fqLogicalZ_cent hStab
  have hcX := parity_commutes_of_InStab (P := fqParams) fqLogicalX fqLogicalX_cent hStab
  rcases h.2 with hZ | hX
  · exact absurd (hZ.symm.trans hcZ) (by decide)
  · exact absurd (hX.symm.trans hcX) (by decide)

end QStab.Examples.FiveQubitNoGo
