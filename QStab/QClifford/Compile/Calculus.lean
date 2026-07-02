import QStab.QClifford.SurfaceD3Distance
import QStab.QClifford.Standard
import QStab.QClifford.Knill
import QStab.QClifford.Shor
import QStab.QClifford.FaultHoareCompleteness
import QStab.QHL.Target.Deriv

/-!
# QClifford compilation calculus

This module packages the stabilizer-measurement compiler as explicit rules.
The rules below produce instrumented QClifford circuits: a one-qubit operation
`U(q)` compiles as `!q; U(q)`, and a two-qubit operation `CX(c,t)` compiles as
`!c; !t; CX(c,t)`.  These `!q` sites are the concrete single-location Pauli
fault locations consumed by the QClifford fault semantics.

Rules, with `flagMeasZ` recording the genuine Z-basis measurement bit in the
time-resolved detector log:

```text
NZ-X:    prepP(a); CX(a,q_i) for q_i in sigma; H(a); flagMeasZ(a)
NZ-Z:    prep0(a); CX(q_i,a) for q_i in sigma; flagMeasZ(a)

Knill:   for q_i in sigma:
           prep0(a_i); CX(q_i,a_i); rawMeasZ(a_i)
         The stabilizer flag is the XOR of the raw outcomes.

Shor:    cat-prep(c); prepP(v); CX(v,c_0); CX(v,c_last); H(v); flagMeasZ(v);
         zParitySlot(c_i, sigma_i); rawMeasZ(c_i)
         The stabilizer flag is the XOR of the raw cat measurements.

Flag-X:  prepP(a); prep0(f);
         CX(a,sigma[0..m)); CX(a,f); CX(a,sigma[m..));
         CX(a,f); H(a); flagMeasZ(a); flagMeasZ(f)
```

The NZ equations are used by the closed surface-d3 PCC client; the other scheme
equations are first-class syntax for the same circuit families already present
in `Standard`, `Knill`, `Shor`, and `FlagGeneral`.
-/

namespace QStab.QClifford.Compile

open QStab.QClifford

inductive Scheme where
  | NZ
  | Knill
  | Shor
  | Flag
  deriving DecidableEq, Repr

/-- X/Z Pauli labels accepted by the fresh ordered compiler.

The current QClifford gate language has CNOT, H, prep0/prep+, and Z
measurement, but no phase gate.  The strict compiler therefore exposes only
X/Z measurement slots.  A source stabilizer with an `I` entry omits that qubit
from the schedule; a source stabilizer with a `Y` entry needs a future rule
after the gate language grows a phase gate. -/
inductive XZPauli where
  | X
  | Z
  deriving DecidableEq, Repr

def XZPauli.toPauli : XZPauli -> Pauli
  | .X => .X
  | .Z => .Z

/-- One written stabilizer slot: first the Pauli label, then the data qubit.
The list order is the syndrome-extraction schedule. -/
structure ScheduledPauli (nq : Nat) where
  kind : XZPauli
  qubit : Fin nq
  deriving DecidableEq, Repr

/-- Ordered, Pauli-labelled schedule for a single stabilizer measurement. -/
structure RuleSchedule (nq : Nat) where
  slots : List (ScheduledPauli nq)
  deriving DecidableEq, Repr

structure Schedule (nq : Nat) where
  support : List (Fin nq)
  deriving Repr

namespace RuleSchedule

def support {nq : Nat} (sigma : RuleSchedule nq) : List (Fin nq) :=
  sigma.slots.map (fun slot => slot.qubit)

def paulis {nq : Nat} (sigma : RuleSchedule nq) : List XZPauli :=
  sigma.slots.map (fun slot => slot.kind)

def uniform {nq : Nat} (kind : XZPauli) (support : List (Fin nq)) :
    RuleSchedule nq :=
  ⟨support.map (fun q => ⟨kind, q⟩)⟩

end RuleSchedule

inductive AncillaConfig (nq : Nat) where
  | nz (anc : Fin nq)
  | knill (ancillas : List (Fin nq))
  | shor (cat : List (Fin nq)) (verifier : Fin nq)
  | flag (anc flag : Fin nq)
  deriving Repr

def rawMeasZ {nq : Nat} (q : Fin nq) : FCircuit nq :=
  [.errLoc q, .gate (.measZ q)]

def flagMeasZ {nq : Nat} (q : Fin nq) : FCircuit nq :=
  [.errLoc q, .gate (.measZ q)]

def prep0 {nq : Nat} (q : Fin nq) : FCircuit nq :=
  [.errLoc q, .gate (.prepZero q)]

def prepP {nq : Nat} (q : Fin nq) : FCircuit nq :=
  [.errLoc q, .gate (.prepPlus q)]

def hadamard {nq : Nat} (q : Fin nq) : FCircuit nq :=
  [.errLoc q, .gate (.hadamard q)]

def cnot {nq : Nat} (c t : Fin nq) : FCircuit nq :=
  if h : c = t then
    []
  else
    [.errLoc c, .errLoc t, .gate (.cnot c t h)]

/-- Data qubit `q` embedded in a fresh-helper layout with `n` data qubits
and `k` helper qubits. -/
def freshDataQ (n k : Nat) (q : Fin n) : Fin (n + k) :=
  ⟨q.val, by have := q.isLt; omega⟩

/-- Helper qubit at helper offset `a`, globally indexed as `n + a`. -/
def freshHelperQ (n k : Nat) (a : Fin k) : Fin (n + k) :=
  ⟨n + a.val, by have := a.isLt; omega⟩

@[simp] theorem freshDataQ_val {n k : Nat} (q : Fin n) :
    (freshDataQ n k q).val = q.val := rfl

@[simp] theorem freshHelperQ_val {n k : Nat} (a : Fin k) :
    (freshHelperQ n k a).val = n + a.val := rfl

theorem freshDataQ_ne_freshHelperQ {n k : Nat} (q : Fin n) (a : Fin k) :
    freshDataQ n k q ≠ freshHelperQ n k a := by
  intro h
  have hv := congrArg Fin.val h
  simp [freshDataQ, freshHelperQ] at hv
  have hq := q.isLt
  omega

def liftSlot {n k : Nat} (slot : ScheduledPauli n) : ScheduledPauli (n + k) :=
  ⟨slot.kind, freshDataQ n k slot.qubit⟩

def liftSchedule {n k : Nat} (sigma : RuleSchedule n) : RuleSchedule (n + k) :=
  ⟨sigma.slots.map liftSlot⟩

/-- Number of fresh helper qubits allocated by one stabilizer gadget. -/
def helperCount {n : Nat} (scheme : Scheme) (sigma : RuleSchedule n) : Nat :=
  match scheme with
  | .NZ => 1
  | .Knill => sigma.slots.length
  | .Shor => sigma.slots.length + 1
  | .Flag => 2

def freshKnillAncillas (n : Nat) (w : Nat) : List (Fin (n + w)) :=
  (List.finRange w).map (freshHelperQ n w)

def freshShorCat (n w : Nat) : List (Fin (n + (w + 1))) :=
  (List.finRange w).map (fun a =>
    freshHelperQ n (w + 1) ⟨a.val, by exact Nat.lt_trans a.isLt (Nat.lt_succ_self w)⟩)

theorem freshShorCat_nodup (n w : Nat) : (freshShorCat n w).Nodup := by
  unfold freshShorCat
  refine List.Nodup.map ?_ (List.nodup_finRange w)
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [freshHelperQ] at hv
  omega

theorem mem_freshShorCat_helper {n w : Nat} {q : Fin (n + (w + 1))}
    (hmem : q ∈ freshShorCat n w) :
    ∃ a : Fin w,
      q = freshHelperQ n (w + 1)
        ⟨a.val, by exact Nat.lt_trans a.isLt (Nat.lt_succ_self w)⟩ := by
  have hmem' :
      q ∈ (List.finRange w).map (fun a =>
        freshHelperQ n (w + 1)
          ⟨a.val, by exact Nat.lt_trans a.isLt (Nat.lt_succ_self w)⟩) := by
    simpa [freshShorCat] using hmem
  rcases List.mem_map.mp hmem' with ⟨a, _ha, rfl⟩
  exact ⟨a, rfl⟩

def freshAncillaConfig {n : Nat} (scheme : Scheme) (sigma : RuleSchedule n) :
    AncillaConfig (n + helperCount scheme sigma) :=
  match scheme with
  | .NZ =>
      .nz (freshHelperQ n 1 ⟨0, by decide⟩)
  | .Knill =>
      .knill (freshKnillAncillas n sigma.slots.length)
  | .Shor =>
      let w := sigma.slots.length
      .shor (freshShorCat n w) (freshHelperQ n (w + 1) ⟨w, Nat.lt_succ_self w⟩)
  | .Flag =>
      .flag (freshHelperQ n 2 ⟨0, by decide⟩)
        (freshHelperQ n 2 ⟨1, by decide⟩)

def freshRuleSchedule {n : Nat} (scheme : Scheme) (sigma : RuleSchedule n) :
    RuleSchedule (n + helperCount scheme sigma) :=
  liftSchedule (k := helperCount scheme sigma) sigma

/-- Gate trace used by executable regression examples.  It forgets proof
objects in CNOT gates but keeps the ordered qubit-level circuit shape. -/
inductive RuleTrace where
  | errLoc (q : Nat)
  | prepZero (q : Nat)
  | prepPlus (q : Nat)
  | hadamard (q : Nat)
  | cnot (control target : Nat)
  | measZ (q : Nat)
  deriving DecidableEq, Repr

def traceInstr {nq : Nat} : FInstr nq -> RuleTrace
  | .errLoc q => .errLoc q.val
  | .gate (.prepZero q) => .prepZero q.val
  | .gate (.prepPlus q) => .prepPlus q.val
  | .gate (.hadamard q) => .hadamard q.val
  | .gate (.cnot c t _) => .cnot c.val t.val
  | .gate (.measZ q) => .measZ q.val

def traceCircuit {nq : Nat} (fc : FCircuit nq) : List RuleTrace :=
  fc.map traceInstr

@[simp] theorem eraseFaults_append {nq : Nat} (a b : FCircuit nq) :
    eraseFaults (a ++ b) = eraseFaults a ++ eraseFaults b := by
  induction a with
  | nil => rfl
  | cons i rest ih =>
      cases i <;> simp [eraseFaults, ih]

@[simp] theorem propagateEraseFaults_append {nq : Nat} (a b : FCircuit nq)
    (es : ErrorState nq) :
    propagateCircuit (eraseFaults (a ++ b)) es =
      propagateCircuit (eraseFaults b) (propagateCircuit (eraseFaults a) es) := by
  rw [eraseFaults_append, QHL.Target.propagateCircuit_append]

theorem eraseFaults_flatten {nq : Nat} (chunks : List (FCircuit nq)) :
    eraseFaults chunks.flatten = (chunks.map eraseFaults).flatten := by
  induction chunks with
  | nil => rfl
  | cons c rest ih =>
      simp [List.flatten, ih, eraseFaults_append]

theorem propagateCircuit_flatten {nq : Nat} (chunks : List (Circuit nq))
    (es : ErrorState nq) :
    propagateCircuit chunks.flatten es =
      chunks.foldl (fun es' c => propagateCircuit c es') es := by
  induction chunks generalizing es with
  | nil => rfl
  | cons c rest ih =>
      simp [List.flatten, QHL.Target.propagateCircuit_append, ih]

theorem eraseFaults_append8 {nq : Nat}
    (a b c d e f g h : FCircuit nq) :
    eraseFaults (a ++ b ++ c ++ d ++ e ++ f ++ g ++ h) =
      eraseFaults a ++ eraseFaults b ++ eraseFaults c ++ eraseFaults d ++
        eraseFaults e ++ eraseFaults f ++ eraseFaults g ++ eraseFaults h := by
  simp [eraseFaults_append]

theorem propagateCircuit_append8 {nq : Nat}
    (a b c d e f g h : Circuit nq) (es : ErrorState nq) :
    propagateCircuit (a ++ b ++ c ++ d ++ e ++ f ++ g ++ h) es =
      propagateCircuit h
        (propagateCircuit g
          (propagateCircuit f
            (propagateCircuit e
              (propagateCircuit d
                (propagateCircuit c
                  (propagateCircuit b (propagateCircuit a es))))))) := by
  simp [QHL.Target.propagateCircuit_append]

@[simp] theorem eraseFaults_cnot {nq : Nat} (c t : Fin nq) (h : c ≠ t) :
    eraseFaults (cnot c t) = [Gate.cnot c t h] := by
  simp [cnot, h]

def zParitySlot {nq : Nat} (anc : Fin nq) (slot : ScheduledPauli nq) :
    FCircuit nq :=
  match slot.kind with
  | .X => hadamard slot.qubit ++ cnot slot.qubit anc ++ hadamard slot.qubit
  | .Z => cnot slot.qubit anc

/-- Standard fresh CNOT rule for an ordered X/Z Pauli product.

The ancilla is prepared in the Z basis.  Z slots use `CX(data, anc)`;
X slots are first rotated into the Z basis by surrounding that CNOT with
Hadamards on the data qubit. -/
def compileStandardOrdered {nq : Nat} (sigma : RuleSchedule nq) (anc : Fin nq) :
    FCircuit nq :=
  prep0 anc ++
  (sigma.slots.map (zParitySlot anc)).flatten ++
  flagMeasZ anc

def knillSlot {nq : Nat} (slot : ScheduledPauli nq) (anc : Fin nq) :
    FCircuit nq :=
  prep0 anc ++ zParitySlot anc slot ++ rawMeasZ anc

/-- Knill-style ordered rule: allocate one fresh helper for each written slot.
The stabilizer bit is the XOR of the raw helper measurements. -/
def compileKnillOrdered {nq : Nat} (sigma : RuleSchedule nq)
    (ancillas : List (Fin nq)) : FCircuit nq :=
  ((List.zip sigma.slots ancillas).map (fun sa => knillSlot sa.1 sa.2)).flatten

def shorCouplingSlot {nq : Nat} (slot : ScheduledPauli nq) (cat : Fin nq) :
    FCircuit nq :=
  match slot.kind with
  | .X => hadamard slot.qubit ++ cnot slot.qubit cat ++ hadamard slot.qubit
  | .Z => cnot slot.qubit cat

def orderedCatPrepZ {nq : Nat} (cat : List (Fin nq)) : FCircuit nq :=
  match cat with
  | [] => []
  | c0 :: rest =>
      prep0 c0 ++
      ((List.zip (c0 :: rest) rest).map (fun cc => cnot cc.1 cc.2)).flatten

/-- Shor cat-state ordered rule with one cat helper per written slot and one
fresh verifier helper.  The stabilizer bit is the XOR of the raw cat
measurements, with the verifier measurement available as the cat-check flag. -/
def compileShorOrdered {nq : Nat} (sigma : RuleSchedule nq)
    (cat : List (Fin nq)) (verifier : Fin nq) : FCircuit nq :=
  match cat with
  | [] => []
  | c0 :: rest =>
      let cat' := c0 :: rest
      let last := cat'.getLast (by simp)
      orderedCatPrepZ cat' ++
      prepP verifier ++
      cnot verifier c0 ++
      cnot verifier last ++
      hadamard verifier ++
      flagMeasZ verifier ++
      ((List.zip sigma.slots cat').map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten ++
      (cat'.map rawMeasZ).flatten

/-- Single-flag ordered rule in the same Z-parity orientation as
`compileStandardOrdered`.  The two flag couplings bracket the written order.
This is the syntactic compiler rule; the mixed-X/Z flag bounded-hook theorem is
a separate proof obligation. -/
def compileFlagOrdered {nq : Nat} (sigma : RuleSchedule nq)
    (anc flag : Fin nq) : FCircuit nq :=
  let half := sigma.slots.length / 2
  prep0 anc ++
  prepP flag ++
  ((sigma.slots.take half).map (zParitySlot anc)).flatten ++
  cnot flag anc ++
  ((sigma.slots.drop half).map (zParitySlot anc)).flatten ++
  cnot flag anc ++
  flagMeasZ anc ++
  hadamard flag ++
  flagMeasZ flag

def compileGadgetOrdered {nq : Nat} (scheme : Scheme)
    (sigma : RuleSchedule nq) (anc : AncillaConfig nq) : FCircuit nq :=
  match scheme, anc with
  | .NZ, .nz a => compileStandardOrdered sigma a
  | .Knill, .knill as => compileKnillOrdered sigma as
  | .Shor, .shor cat verifier => compileShorOrdered sigma cat verifier
  | .Flag, .flag a f => compileFlagOrdered sigma a f
  | _, _ => []

/-! ## Reverse-order compilation derivations

The executable compiler above still returns circuits in execution order.  The
proof-producing compiler, however, should construct those circuits from right
to left: at every rule application the already-built suffix is known, so the
rule can compute the current detector/back-action effect of faults introduced
by the newly prepended fragment.

The derivations below are the PL-style rule skeleton for that proof-producing
compiler.  A `prepend` node adds the next source-scheduled fragment in front of
an already compiled suffix; the accompanying equality lemmas pin the derivation
to the executable compiler equations consumed by VCGen.
-/

/-- Reverse derivation for a concrete instrumented circuit: build the suffix
first, then prepend one instruction. -/
inductive ReverseCircuitDeriv {nq : Nat} : FCircuit nq -> FCircuit nq -> Type where
  | nil : ReverseCircuitDeriv [] []
  | prepend {instr : FInstr nq} {rest suffix : FCircuit nq} :
      ReverseCircuitDeriv rest suffix ->
        ReverseCircuitDeriv (instr :: rest) (instr :: suffix)

namespace ReverseCircuitDeriv

theorem circuit_eq {nq : Nat} {fc circuit : FCircuit nq}
    (d : ReverseCircuitDeriv fc circuit) : circuit = fc := by
  induction d with
  | nil => rfl
  | prepend _ ih =>
      simp [ih]

def ofCircuit {nq : Nat} : (fc : FCircuit nq) -> ReverseCircuitDeriv fc fc
  | [] => .nil
  | _ :: rest => .prepend (ofCircuit rest)

end ReverseCircuitDeriv

/-- Reverse derivation for `(xs.map chunk).flatten`: recursively compile the
tail first, then prepend the chunk for the next written schedule element. -/
inductive ReverseFlattenMapDeriv {nq : Nat} {α : Type}
    (chunk : α -> FCircuit nq) : List α -> FCircuit nq -> Type where
  | nil : ReverseFlattenMapDeriv chunk [] []
  | prepend {x : α} {xs : List α} {suffix : FCircuit nq} :
      ReverseFlattenMapDeriv chunk xs suffix ->
        ReverseFlattenMapDeriv chunk (x :: xs) (chunk x ++ suffix)

namespace ReverseFlattenMapDeriv

theorem circuit_eq {nq : Nat} {α : Type} {chunk : α -> FCircuit nq}
    {xs : List α} {circuit : FCircuit nq}
    (d : ReverseFlattenMapDeriv chunk xs circuit) :
    circuit = (xs.map chunk).flatten := by
  induction d with
  | nil => rfl
  | prepend _ ih =>
      simp [ih]

def ofList {nq : Nat} {α : Type} (chunk : α -> FCircuit nq) :
    (xs : List α) -> ReverseFlattenMapDeriv chunk xs (xs.map chunk).flatten
  | [] => .nil
  | x :: xs => by
      simpa [List.flatten] using
        ReverseFlattenMapDeriv.prepend (ofList chunk xs)

end ReverseFlattenMapDeriv

/-- Reverse rule family for the standard/NZ stabilizer interactions.  The base
suffix is the final readout; each rule prepends the next written Pauli slot. -/
inductive StandardReverseSlotsDeriv {nq : Nat} (anc : Fin nq) :
    List (ScheduledPauli nq) -> FCircuit nq -> Type where
  | readout : StandardReverseSlotsDeriv anc [] (flagMeasZ anc)
  | prependSlot {slot : ScheduledPauli nq} {slots : List (ScheduledPauli nq)}
      {suffix : FCircuit nq} :
      StandardReverseSlotsDeriv anc slots suffix ->
        StandardReverseSlotsDeriv anc (slot :: slots) (zParitySlot anc slot ++ suffix)

namespace StandardReverseSlotsDeriv

theorem circuit_eq {nq : Nat} {anc : Fin nq}
    {slots : List (ScheduledPauli nq)} {suffix : FCircuit nq}
    (d : StandardReverseSlotsDeriv anc slots suffix) :
    suffix = (slots.map (zParitySlot anc)).flatten ++ flagMeasZ anc := by
  induction d with
  | readout =>
      rfl
  | prependSlot _ ih =>
      simp [ih, List.append_assoc]

def ofSlots {nq : Nat} (anc : Fin nq) :
    (slots : List (ScheduledPauli nq)) ->
      StandardReverseSlotsDeriv anc slots
        ((slots.map (zParitySlot anc)).flatten ++ flagMeasZ anc)
  | [] => by
      simpa using StandardReverseSlotsDeriv.readout (anc := anc)
  | slot :: slots => by
      simpa [List.flatten, List.append_assoc] using
        StandardReverseSlotsDeriv.prependSlot (ofSlots anc slots)

end StandardReverseSlotsDeriv

/-- Complete reverse derivation for the standard/NZ scheme. -/
inductive StandardReverseCompileDeriv {nq : Nat}
    (sigma : RuleSchedule nq) (anc : Fin nq) : FCircuit nq -> Type where
  | prependPrep {suffix : FCircuit nq} :
      StandardReverseSlotsDeriv anc sigma.slots suffix ->
        StandardReverseCompileDeriv sigma anc (prep0 anc ++ suffix)

namespace StandardReverseCompileDeriv

theorem circuit_eq {nq : Nat} {sigma : RuleSchedule nq} {anc : Fin nq}
    {circuit : FCircuit nq} (d : StandardReverseCompileDeriv sigma anc circuit) :
    circuit = compileStandardOrdered sigma anc := by
  cases d with
  | prependPrep slots =>
      have hslots := slots.circuit_eq
      simp [compileStandardOrdered, hslots]

def ofSchedule {nq : Nat} (sigma : RuleSchedule nq) (anc : Fin nq) :
    StandardReverseCompileDeriv sigma anc (compileStandardOrdered sigma anc) := by
  simpa [compileStandardOrdered] using
    StandardReverseCompileDeriv.prependPrep
      (StandardReverseSlotsDeriv.ofSlots anc sigma.slots)

end StandardReverseCompileDeriv

abbrev KnillReverseCompileDeriv {nq : Nat}
    (sigma : RuleSchedule nq) (ancillas : List (Fin nq)) (circuit : FCircuit nq) : Type :=
  ReverseFlattenMapDeriv
    (fun sa : ScheduledPauli nq × Fin nq => knillSlot sa.1 sa.2)
    (List.zip sigma.slots ancillas) circuit

def compileKnillOrderedReverseDeriv {nq : Nat}
    (sigma : RuleSchedule nq) (ancillas : List (Fin nq)) :
    KnillReverseCompileDeriv sigma ancillas (compileKnillOrdered sigma ancillas) := by
  simpa [compileKnillOrdered] using
    ReverseFlattenMapDeriv.ofList
      (fun sa : ScheduledPauli nq × Fin nq => knillSlot sa.1 sa.2)
      (List.zip sigma.slots ancillas)

abbrev ShorCouplingReverseDeriv {nq : Nat}
    (sigma : RuleSchedule nq) (cat : List (Fin nq)) (circuit : FCircuit nq) : Type :=
  ReverseFlattenMapDeriv
    (fun sc : ScheduledPauli nq × Fin nq => shorCouplingSlot sc.1 sc.2)
    (List.zip sigma.slots cat) circuit

def shorCouplingReverseDeriv {nq : Nat}
    (sigma : RuleSchedule nq) (cat : List (Fin nq)) :
    ShorCouplingReverseDeriv sigma cat
      (((List.zip sigma.slots cat).map (fun sc => shorCouplingSlot sc.1 sc.2)).flatten) :=
  ReverseFlattenMapDeriv.ofList
    (fun sc : ScheduledPauli nq × Fin nq => shorCouplingSlot sc.1 sc.2)
    (List.zip sigma.slots cat)

abbrev RawMeasReverseDeriv {nq : Nat}
    (qs : List (Fin nq)) (circuit : FCircuit nq) : Type :=
  ReverseFlattenMapDeriv rawMeasZ qs circuit

def rawMeasReverseDeriv {nq : Nat} (qs : List (Fin nq)) :
    RawMeasReverseDeriv qs (qs.map rawMeasZ).flatten :=
  ReverseFlattenMapDeriv.ofList rawMeasZ qs

/-- Complete reverse derivation for the Shor scheme.  The interaction and raw
measurement tails are themselves reverse list derivations; the fixed cat-check
prefix is then prepended to the known suffix. -/
inductive ShorReverseCompileDeriv {nq : Nat}
    (sigma : RuleSchedule nq) (cat : List (Fin nq)) (verifier : Fin nq) :
    FCircuit nq -> Type where
  | nilCat : cat = [] -> ShorReverseCompileDeriv sigma cat verifier []
  | consCat (c0 : Fin nq) (rest : List (Fin nq))
      (hcat : cat = c0 :: rest)
      {coupling raw : FCircuit nq} :
      ShorCouplingReverseDeriv sigma (c0 :: rest) coupling ->
        RawMeasReverseDeriv (c0 :: rest) raw ->
          ShorReverseCompileDeriv sigma cat verifier
            (let cat' := c0 :: rest
             let last := cat'.getLast (by simp)
             orderedCatPrepZ cat' ++
             prepP verifier ++
             cnot verifier c0 ++
             cnot verifier last ++
             hadamard verifier ++
             flagMeasZ verifier ++
             coupling ++ raw)

namespace ShorReverseCompileDeriv

theorem circuit_eq {nq : Nat} {sigma : RuleSchedule nq}
    {cat : List (Fin nq)} {verifier : Fin nq} {circuit : FCircuit nq}
    (d : ShorReverseCompileDeriv sigma cat verifier circuit) :
    circuit = compileShorOrdered sigma cat verifier := by
  cases d with
  | nilCat hcat =>
      subst hcat
      rfl
  | consCat c0 rest hcat couplingDeriv rawDeriv =>
      subst hcat
      have hcoupling := couplingDeriv.circuit_eq
      have hraw := rawDeriv.circuit_eq
      simp [compileShorOrdered, hcoupling, hraw, List.append_assoc]

def ofSchedule {nq : Nat}
    (sigma : RuleSchedule nq) (cat : List (Fin nq)) (verifier : Fin nq) :
    ShorReverseCompileDeriv sigma cat verifier (compileShorOrdered sigma cat verifier) := by
  cases cat with
  | nil =>
      exact ShorReverseCompileDeriv.nilCat rfl
  | cons c0 rest =>
      simpa [compileShorOrdered, List.append_assoc] using
        ShorReverseCompileDeriv.consCat (sigma := sigma) (verifier := verifier)
          c0 rest rfl
          (shorCouplingReverseDeriv sigma (c0 :: rest))
          (rawMeasReverseDeriv (c0 :: rest))

end ShorReverseCompileDeriv

/-- Reverse derivation for the flag scheme.  The two halves are separate list
derivations so the rule remembers the written schedule order around the flag
couplings. -/
inductive FlagReverseCompileDeriv {nq : Nat}
    (sigma : RuleSchedule nq) (anc flag : Fin nq) : FCircuit nq -> Type where
  | build
      {firstHalf secondHalf : FCircuit nq}
      (half : Nat)
      (hhalf : half = sigma.slots.length / 2)
      (first :
        ReverseFlattenMapDeriv (zParitySlot anc) (sigma.slots.take half) firstHalf)
      (second :
        ReverseFlattenMapDeriv (zParitySlot anc) (sigma.slots.drop half) secondHalf) :
      FlagReverseCompileDeriv sigma anc flag
        (prep0 anc ++
         prepP flag ++
         firstHalf ++
         cnot flag anc ++
         secondHalf ++
         cnot flag anc ++
         flagMeasZ anc ++
         hadamard flag ++
         flagMeasZ flag)

namespace FlagReverseCompileDeriv

theorem circuit_eq {nq : Nat} {sigma : RuleSchedule nq}
    {anc flag : Fin nq} {circuit : FCircuit nq}
    (d : FlagReverseCompileDeriv sigma anc flag circuit) :
    circuit = compileFlagOrdered sigma anc flag := by
  cases d with
  | build half hhalf first second =>
      subst hhalf
      have hfirst := first.circuit_eq
      have hsecond := second.circuit_eq
      simp [compileFlagOrdered, hfirst, hsecond, List.append_assoc]

def ofSchedule {nq : Nat}
    (sigma : RuleSchedule nq) (anc flag : Fin nq) :
    FlagReverseCompileDeriv sigma anc flag (compileFlagOrdered sigma anc flag) := by
  let half := sigma.slots.length / 2
  simpa [compileFlagOrdered, half, List.append_assoc] using
    FlagReverseCompileDeriv.build (sigma := sigma) (anc := anc) (flag := flag)
      half rfl
      (ReverseFlattenMapDeriv.ofList (zParitySlot anc) (sigma.slots.take half))
      (ReverseFlattenMapDeriv.ofList (zParitySlot anc) (sigma.slots.drop half))

end FlagReverseCompileDeriv

/-- Scheme dispatcher for reverse compilation derivations. -/
inductive GadgetReverseCompileDeriv {nq : Nat}
    (scheme : Scheme) (sigma : RuleSchedule nq) (anc : AncillaConfig nq) :
    FCircuit nq -> Type where
  | nz (a : Fin nq) :
      scheme = .NZ ->
        anc = .nz a ->
          StandardReverseCompileDeriv sigma a (compileStandardOrdered sigma a) ->
            GadgetReverseCompileDeriv scheme sigma anc (compileStandardOrdered sigma a)
  | knill (ancillas : List (Fin nq)) :
      scheme = .Knill ->
        anc = .knill ancillas ->
          KnillReverseCompileDeriv sigma ancillas (compileKnillOrdered sigma ancillas) ->
            GadgetReverseCompileDeriv scheme sigma anc (compileKnillOrdered sigma ancillas)
  | shor (cat : List (Fin nq)) (verifier : Fin nq) :
      scheme = .Shor ->
        anc = .shor cat verifier ->
          ShorReverseCompileDeriv sigma cat verifier (compileShorOrdered sigma cat verifier) ->
            GadgetReverseCompileDeriv scheme sigma anc (compileShorOrdered sigma cat verifier)
  | flag (a f : Fin nq) :
      scheme = .Flag ->
        anc = .flag a f ->
          FlagReverseCompileDeriv sigma a f (compileFlagOrdered sigma a f) ->
            GadgetReverseCompileDeriv scheme sigma anc (compileFlagOrdered sigma a f)
  | mismatch :
      compileGadgetOrdered scheme sigma anc = [] ->
        GadgetReverseCompileDeriv scheme sigma anc []

namespace GadgetReverseCompileDeriv

theorem circuit_eq {nq : Nat} {scheme : Scheme} {sigma : RuleSchedule nq}
    {anc : AncillaConfig nq} {circuit : FCircuit nq}
    (d : GadgetReverseCompileDeriv scheme sigma anc circuit) :
    circuit = compileGadgetOrdered scheme sigma anc := by
  cases d with
  | nz a hscheme hanc _ =>
      subst hscheme
      subst hanc
      simp [compileGadgetOrdered]
  | knill ancillas hscheme hanc _ =>
      subst hscheme
      subst hanc
      simp [compileGadgetOrdered]
  | shor cat verifier hscheme hanc _ =>
      subst hscheme
      subst hanc
      simp [compileGadgetOrdered]
  | flag a f hscheme hanc _ =>
      subst hscheme
      subst hanc
      simp [compileGadgetOrdered]
  | mismatch h =>
      exact h.symm

def ofOrdered {nq : Nat} (scheme : Scheme)
    (sigma : RuleSchedule nq) (anc : AncillaConfig nq) :
    GadgetReverseCompileDeriv scheme sigma anc (compileGadgetOrdered scheme sigma anc) := by
  cases scheme <;> cases anc
  · exact GadgetReverseCompileDeriv.nz _ rfl rfl
      (StandardReverseCompileDeriv.ofSchedule sigma _)
  · exact GadgetReverseCompileDeriv.mismatch rfl
  · exact GadgetReverseCompileDeriv.mismatch rfl
  · exact GadgetReverseCompileDeriv.mismatch rfl
  · exact GadgetReverseCompileDeriv.mismatch rfl
  · exact GadgetReverseCompileDeriv.knill _ rfl rfl
      (compileKnillOrderedReverseDeriv sigma _)
  · exact GadgetReverseCompileDeriv.mismatch rfl
  · exact GadgetReverseCompileDeriv.mismatch rfl
  · exact GadgetReverseCompileDeriv.mismatch rfl
  · exact GadgetReverseCompileDeriv.mismatch rfl
  · exact GadgetReverseCompileDeriv.shor _ _ rfl rfl
      (ShorReverseCompileDeriv.ofSchedule sigma _ _)
  · exact GadgetReverseCompileDeriv.mismatch rfl
  · exact GadgetReverseCompileDeriv.mismatch rfl
  · exact GadgetReverseCompileDeriv.mismatch rfl
  · exact GadgetReverseCompileDeriv.mismatch rfl
  · exact GadgetReverseCompileDeriv.flag _ _ rfl rfl
      (FlagReverseCompileDeriv.ofSchedule sigma _ _)

end GadgetReverseCompileDeriv

/-- Strict compiler entry point for one source stabilizer gadget.  The target
circuit type itself records the fresh helper budget, and the only helper
indices are generated by `freshAncillaConfig`. -/
def compileFreshGadget {n : Nat} (scheme : Scheme) (sigma : RuleSchedule n) :
    FCircuit (n + helperCount scheme sigma) :=
  compileGadgetOrdered scheme (freshRuleSchedule scheme sigma)
    (freshAncillaConfig scheme sigma)

/-- A future preservation theorem should quantify over this syntax, not over an
arbitrary target circuit.  The circuit is computed, not supplied by the user. -/
structure FreshCompiledGadget (n : Nat) where
  scheme : Scheme
  schedule : RuleSchedule n
  deriving Repr

def FreshCompiledGadget.circuit {n : Nat} (G : FreshCompiledGadget n) :
    FCircuit (n + helperCount G.scheme G.schedule) :=
  compileFreshGadget G.scheme G.schedule

/-! ## Full X/Z measurement-program compilation

`XZProgram` is the compiler-facing QStab program fragment for this pass:
it contains only stabilizer measurements over ordered X/Z schedules and
sequential composition.  The target qubit count is computed from the whole
tree, so every measurement receives a disjoint helper block. -/

inductive XZProgram (n : Nat) where
  | skip
  | meas (scheme : Scheme) (schedule : RuleSchedule n)
  | seq (first second : XZProgram n)
  deriving Repr

def programHelperCount {n : Nat} : XZProgram n -> Nat
  | .skip => 0
  | .meas scheme schedule => helperCount scheme schedule
  | .seq first second => programHelperCount first + programHelperCount second

def blockHelperQ (n total start width : Nat) (hfit : start + width ≤ total)
    (a : Fin width) : Fin (n + total) :=
  ⟨n + start + a.val, by have := a.isLt; omega⟩

def blockHelpers (n total start width : Nat) (hfit : start + width ≤ total) :
    List (Fin (n + total)) :=
  (List.finRange width).map (blockHelperQ n total start width hfit)

def blockShorCat (n total start w : Nat) (hfit : start + (w + 1) ≤ total) :
    List (Fin (n + total)) :=
  (List.finRange w).map (fun a =>
    blockHelperQ n total start (w + 1) hfit
      ⟨a.val, by exact Nat.lt_trans a.isLt (Nat.lt_succ_self w)⟩)

def blockAncillaConfig {n total : Nat} (scheme : Scheme) (sigma : RuleSchedule n)
    (start : Nat) (hfit : start + helperCount scheme sigma ≤ total) :
    AncillaConfig (n + total) :=
  match scheme with
  | .NZ =>
      .nz (blockHelperQ n total start 1 hfit ⟨0, by decide⟩)
  | .Knill =>
      .knill (blockHelpers n total start sigma.slots.length hfit)
  | .Shor =>
      let w := sigma.slots.length
      .shor (blockShorCat n total start w hfit)
        (blockHelperQ n total start (w + 1) hfit ⟨w, Nat.lt_succ_self w⟩)
  | .Flag =>
      .flag (blockHelperQ n total start 2 hfit ⟨0, by decide⟩)
        (blockHelperQ n total start 2 hfit ⟨1, by decide⟩)

def compileGadgetBlock {n total : Nat} (scheme : Scheme) (sigma : RuleSchedule n)
    (start : Nat) (hfit : start + helperCount scheme sigma ≤ total) :
    FCircuit (n + total) :=
  compileGadgetOrdered scheme (liftSchedule (k := total) sigma)
    (blockAncillaConfig scheme sigma start hfit)

def compileFreshGadgetReverseDeriv {n : Nat} (scheme : Scheme) (sigma : RuleSchedule n) :
    GadgetReverseCompileDeriv scheme (freshRuleSchedule scheme sigma)
      (freshAncillaConfig scheme sigma) (compileFreshGadget scheme sigma) := by
  simpa [compileFreshGadget] using
    GadgetReverseCompileDeriv.ofOrdered scheme
      (freshRuleSchedule scheme sigma) (freshAncillaConfig scheme sigma)

def compileGadgetBlockReverseDeriv {n total : Nat}
    (scheme : Scheme) (sigma : RuleSchedule n)
    (start : Nat) (hfit : start + helperCount scheme sigma ≤ total) :
    GadgetReverseCompileDeriv scheme (liftSchedule (k := total) sigma)
      (blockAncillaConfig scheme sigma start hfit)
      (compileGadgetBlock scheme sigma start hfit) := by
  simpa [compileGadgetBlock] using
    GadgetReverseCompileDeriv.ofOrdered scheme (liftSchedule (k := total) sigma)
      (blockAncillaConfig scheme sigma start hfit)

def compileProgramAux {n total : Nat} :
    (start : Nat) -> (program : XZProgram n) ->
      start + programHelperCount program ≤ total -> FCircuit (n + total)
  | _, .skip, _ => []
  | start, .meas scheme sigma, hfit => compileGadgetBlock scheme sigma start hfit
  | start, .seq first second, hfit =>
      compileProgramAux start first (by simp [programHelperCount] at hfit ⊢; omega) ++
      compileProgramAux (start + programHelperCount first) second
        (by simp [programHelperCount] at hfit ⊢; omega)

def compileProgram {n : Nat} (program : XZProgram n) :
    FCircuit (n + programHelperCount program) :=
  compileProgramAux 0 program (by simp)

inductive ProgramCompileDeriv {n total : Nat} :
    Nat -> XZProgram n -> FCircuit (n + total) -> Type where
  | skip (start : Nat) (hfit : start ≤ total) :
      ProgramCompileDeriv start .skip []
  | meas (start : Nat) (scheme : Scheme) (sigma : RuleSchedule n)
      (hfit : start + helperCount scheme sigma ≤ total) :
      ProgramCompileDeriv start (.meas scheme sigma)
        (compileGadgetBlock scheme sigma start hfit)
  | seq {start : Nat} {first second : XZProgram n}
      {c1 c2 : FCircuit (n + total)} :
      ProgramCompileDeriv start first c1 ->
      ProgramCompileDeriv (start + programHelperCount first) second c2 ->
      ProgramCompileDeriv start (.seq first second) (c1 ++ c2)

/-- Full-program reverse compilation derivation.

At a sequence node the second subprogram is derived first, because it is the
known suffix needed when classifying faults introduced by the first subprogram.
The resulting circuit is still the ordinary execution-order concatenation. -/
inductive ProgramReverseCompileDeriv {n total : Nat} :
    Nat -> XZProgram n -> FCircuit (n + total) -> Type where
  | skip (start : Nat) (hfit : start ≤ total) :
      ProgramReverseCompileDeriv start .skip []
  | meas (start : Nat) (scheme : Scheme) (sigma : RuleSchedule n)
      (hfit : start + helperCount scheme sigma ≤ total) :
      GadgetReverseCompileDeriv scheme (liftSchedule (k := total) sigma)
        (blockAncillaConfig scheme sigma start hfit)
        (compileGadgetBlock scheme sigma start hfit) ->
          ProgramReverseCompileDeriv start (.meas scheme sigma)
            (compileGadgetBlock scheme sigma start hfit)
  | seq {start : Nat} {first second : XZProgram n}
      {c1 c2 : FCircuit (n + total)} :
      ProgramReverseCompileDeriv
        (start + programHelperCount first) second c2 ->
      ProgramReverseCompileDeriv start first c1 ->
        ProgramReverseCompileDeriv start (.seq first second) (c1 ++ c2)

def compileProgramAuxDeriv {n total : Nat} :
    (start : Nat) -> (program : XZProgram n) ->
      (hfit : start + programHelperCount program ≤ total) ->
      ProgramCompileDeriv start program (compileProgramAux start program hfit)
  | start, .skip, hfit => by
      exact ProgramCompileDeriv.skip start (by simpa [programHelperCount] using hfit)
  | start, .meas scheme sigma, hfit => ProgramCompileDeriv.meas start scheme sigma hfit
  | start, .seq first second, hfit => by
      exact ProgramCompileDeriv.seq
        (compileProgramAuxDeriv start first
          (by simp [programHelperCount] at hfit ⊢; omega))
        (compileProgramAuxDeriv (start + programHelperCount first) second
          (by simp [programHelperCount] at hfit ⊢; omega))

def compileProgramDeriv {n : Nat} (program : XZProgram n) :
    ProgramCompileDeriv 0 program (compileProgram program) :=
  compileProgramAuxDeriv 0 program (by simp)

def compileProgramAuxReverseDeriv {n total : Nat} :
    (start : Nat) -> (program : XZProgram n) ->
      (hfit : start + programHelperCount program ≤ total) ->
      ProgramReverseCompileDeriv start program (compileProgramAux start program hfit)
  | start, .skip, hfit => by
      exact ProgramReverseCompileDeriv.skip start (by simpa [programHelperCount] using hfit)
  | start, .meas scheme sigma, hfit =>
      ProgramReverseCompileDeriv.meas start scheme sigma hfit
        (compileGadgetBlockReverseDeriv scheme sigma start hfit)
  | start, .seq first second, hfit => by
      exact ProgramReverseCompileDeriv.seq
        (compileProgramAuxReverseDeriv (start + programHelperCount first) second
          (by simp [programHelperCount] at hfit ⊢; omega))
        (compileProgramAuxReverseDeriv start first
          (by simp [programHelperCount] at hfit ⊢; omega))

def compileProgramReverseDeriv {n : Nat} (program : XZProgram n) :
    ProgramReverseCompileDeriv 0 program (compileProgram program) :=
  compileProgramAuxReverseDeriv 0 program (by simp)

/-! ## Detector-parity correctness statements

For X/Z stabilizers, the intended functional correctness theorem says that the
readout detector bit is exactly the anticommutation parity between the measured
stabilizer and the input data Pauli.  The definitions below state that theorem
for one gadget and for a full compiled program. -/

def dataInputState {n k : Nat} (E : Fin n -> Pauli) : ErrorState (n + k) where
  paulis := fun q => if h : q.val < n then E ⟨q.val, h⟩ else Pauli.I
  measFlips := fun _ => false
  detectors := fun _ => false
  detectorCursor := 0

@[simp] theorem dataInputState_freshDataQ {n k : Nat} (E : Fin n -> Pauli)
    (q : Fin n) :
    (dataInputState (k := k) E).paulis (freshDataQ n k q) = E q := by
  simp [dataInputState, freshDataQ]

@[simp] theorem dataInputState_freshHelperQ {n k : Nat} (E : Fin n -> Pauli)
    (a : Fin k) :
    (dataInputState (k := k) E).paulis (freshHelperQ n k a) = Pauli.I := by
  have hnot : ¬ n + a.val < n := by omega
  simp [dataInputState, freshHelperQ, hnot]

def scheduleParity {n : Nat} (sigma : RuleSchedule n) (E : Fin n -> Pauli) :
    Bool :=
  sigma.slots.foldl
    (fun acc slot => xor acc (anticommute slot.kind.toPauli (E slot.qubit)))
    false

def scheduleParityList {nq : Nat} (slots : List (ScheduledPauli nq))
    (E : Fin nq -> Pauli) (init : Bool) : Bool :=
  slots.foldl
    (fun acc slot => xor acc (anticommute slot.kind.toPauli (E slot.qubit)))
    init

def zParitySlotsCircuit {nq : Nat} (anc : Fin nq)
    (slots : List (ScheduledPauli nq)) : FCircuit nq :=
  (slots.map (zParitySlot anc)).flatten

theorem scheduleParityList_append {nq : Nat}
    (a b : List (ScheduledPauli nq)) (E : Fin nq -> Pauli) (init : Bool) :
    scheduleParityList (a ++ b) E init =
      scheduleParityList b E (scheduleParityList a E init) := by
  induction a generalizing init with
  | nil =>
      rfl
  | cons slot rest ih =>
      simp [scheduleParityList]

theorem scheduleParityList_take_drop {nq : Nat}
    (slots : List (ScheduledPauli nq)) (k : Nat) (E : Fin nq -> Pauli)
    (init : Bool) :
    scheduleParityList (slots.drop k) E
        (scheduleParityList (slots.take k) E init) =
      scheduleParityList slots E init := by
  simpa [List.take_append_drop] using
    (scheduleParityList_append (slots.take k) (slots.drop k) E init).symm

theorem scheduleParityList_liftSchedule_init {n k : Nat}
    (sigma : RuleSchedule n) (E : Fin n -> Pauli) (init : Bool) :
    scheduleParityList (liftSchedule (k := k) sigma).slots
        (fun q => (dataInputState (k := k) E).paulis q) init =
      sigma.slots.foldl
        (fun acc slot => xor acc (anticommute slot.kind.toPauli (E slot.qubit)))
        init := by
  cases sigma with
  | mk slots =>
    induction slots generalizing init with
    | nil =>
        rfl
    | cons slot rest ih =>
        cases slot with
        | mk kind qubit =>
          have htail := ih (xor init (anticommute kind.toPauli (E qubit)))
          simpa [liftSchedule, liftSlot, scheduleParityList] using htail

theorem scheduleParityList_liftSchedule {n k : Nat}
    (sigma : RuleSchedule n) (E : Fin n -> Pauli) :
    scheduleParityList (liftSchedule (k := k) sigma).slots
        (fun q => (dataInputState (k := k) E).paulis q) false =
      scheduleParity sigma E := by
  simpa [scheduleParity] using scheduleParityList_liftSchedule_init (k := k) sigma E false

def readoutOffsets {n : Nat} (scheme : Scheme) (sigma : RuleSchedule n) :
    List Nat :=
  match scheme with
  | .NZ => [0]
  | .Knill => List.range sigma.slots.length
  | .Shor => (List.range sigma.slots.length).map Nat.succ
  | .Flag => [0]

def detectorXor {nq : Nat} (slots : List Nat) (es : ErrorState nq) : Bool :=
  slots.foldl (fun acc slot => xor acc (es.detectors slot)) false

def detectorXorFromAcc {nq : Nat} (start len : Nat) (es : ErrorState nq)
    (init : Bool) : Bool :=
  match len with
  | 0 => init
  | l + 1 => detectorXorFromAcc (start + 1) l es (xor init (es.detectors start))

theorem detectorXorFromAcc_succ_end {nq : Nat} (start len : Nat)
    (es : ErrorState nq) (init : Bool) :
    detectorXorFromAcc start (len + 1) es init =
      xor (detectorXorFromAcc start len es init) (es.detectors (start + len)) := by
  induction len generalizing start init with
  | zero =>
      rfl
  | succ len ih =>
      simpa [detectorXorFromAcc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih (start + 1) (xor init (es.detectors start))

theorem detectorXor_range_eq_fromAcc {nq : Nat} (len : Nat) (es : ErrorState nq) :
    detectorXor (List.range len) es = detectorXorFromAcc 0 len es false := by
  induction len with
  | zero =>
      rfl
  | succ len ih =>
      simp [detectorXor, List.range_succ, detectorXorFromAcc_succ_end]
      exact ih

def knillPairsCircuit {nq : Nat} (pairs : List (ScheduledPauli nq × Fin nq)) :
    FCircuit nq :=
  (pairs.map (fun pair => knillSlot pair.1 pair.2)).flatten

def shorCouplingPairsCircuit {nq : Nat} (pairs : List (ScheduledPauli nq × Fin nq)) :
    FCircuit nq :=
  (pairs.map (fun pair => shorCouplingSlot pair.1 pair.2)).flatten

def rawMeasZPairsCircuit {nq : Nat} (pairs : List (ScheduledPauli nq × Fin nq)) :
    FCircuit nq :=
  (pairs.map (fun pair => rawMeasZ pair.2)).flatten

theorem detectorXor_map_succ_range_eq_fromAcc {nq : Nat}
    (len : Nat) (es : ErrorState nq) :
    detectorXor ((List.range len).map Nat.succ) es =
      detectorXorFromAcc 1 len es false := by
  induction len with
  | zero =>
      rfl
  | succ len ih =>
      simp [detectorXor, List.range_succ, detectorXorFromAcc_succ_end,
        Nat.succ_eq_add_one, Nat.add_comm]
      exact ih

theorem zip_nodup_of_right_nodup {α β : Type} :
    ∀ (as : List α) (bs : List β), bs.Nodup -> (List.zip as bs).Nodup
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: as, b :: bs, hbs => by
      have hb_not : b ∉ bs := by
        have h := hbs
        simp at h
        exact h.1
      have hbs_tail : bs.Nodup := by
        have h := hbs
        simp at h
        exact h.2
      refine List.Nodup.cons ?_ (zip_nodup_of_right_nodup as bs hbs_tail)
      intro hmem
      have hb_mem : b ∈ bs := (List.of_mem_zip hmem).2
      exact hb_not hb_mem

theorem zip_right_eq_implies_eq_of_right_nodup {α β : Type} :
    ∀ (as : List α) (bs : List β), bs.Nodup ->
      ∀ p, p ∈ List.zip as bs ->
        ∀ q, q ∈ List.zip as bs -> p.2 = q.2 -> p = q
  | [], _, _, p, hp, _, _, _ => by cases hp
  | _ :: _, [], _, p, hp, _, _, _ => by simp at hp
  | a :: as, b :: bs, hbs, p, hp, q, hq, hright => by
      have hb_not : b ∉ bs := by
        have h := hbs
        simp at h
        exact h.1
      have hbs_tail : bs.Nodup := by
        have h := hbs
        simp at h
        exact h.2
      simp [List.zip_cons_cons] at hp hq
      rcases hp with hp | hp
      · subst p
        rcases hq with hq | hq
        · subst q
          rfl
        · have hb_mem : b ∈ bs := by
            have hq2 : q.2 ∈ bs := (List.of_mem_zip hq).2
            simpa [← hright] using hq2
          exact False.elim (hb_not hb_mem)
      · rcases hq with hq | hq
        · subst q
          have hb_mem : b ∈ bs := by
            have hp2 : p.2 ∈ bs := (List.of_mem_zip hp).2
            simpa [hright] using hp2
          exact False.elim (hb_not hb_mem)
        · exact zip_right_eq_implies_eq_of_right_nodup as bs hbs_tail p hp q hq hright

theorem zip_right_ne_of_right_nodup {α β : Type} (as : List α) (bs : List β)
    (hbs : bs.Nodup) :
    ∀ p, p ∈ List.zip as bs ->
      ∀ q, q ∈ List.zip as bs -> p ≠ q -> p.2 ≠ q.2 := by
  intro p hp q hq hpq hright
  exact hpq (zip_right_eq_implies_eq_of_right_nodup as bs hbs p hp q hq hright)

def gadgetDetectorBit {n : Nat} (scheme : Scheme) (sigma : RuleSchedule n)
    (es : ErrorState (n + helperCount scheme sigma)) : Bool :=
  detectorXor (readoutOffsets scheme sigma) es

def xOfBool (b : Bool) : Pauli :=
  if b then Pauli.X else Pauli.I

@[simp] theorem xOfBool_false : xOfBool false = Pauli.I := rfl
@[simp] theorem xOfBool_true : xOfBool true = Pauli.X := rfl

@[simp] theorem hasXComp_xOfBool (b : Bool) : hasXComp (xOfBool b) = b := by
  cases b <;> rfl

@[simp] theorem zPart_xOfBool (b : Bool) : zPart (xOfBool b) = Pauli.I := by
  cases b <;> rfl

theorem pauliMul_xOfBool (a b : Bool) :
    pauliMul (xOfBool a) (xOfBool b) = xOfBool (xor a b) := by
  cases a <;> cases b <;> rfl

theorem xOfBool_xor_comm (a b : Bool) :
    xOfBool (xor a b) = xOfBool (xor b a) := by
  cases a <;> cases b <;> rfl

@[simp] theorem hadamardAction_involutive (p : Pauli) :
    hadamardAction (hadamardAction p) = p := by
  cases p <;> rfl

theorem xPart_for_slot (kind : XZPauli) (p : Pauli) :
    xPart (match kind with | .X => hadamardAction p | .Z => p) =
      xOfBool (anticommute kind.toPauli p) := by
  cases kind <;> cases p <;> rfl

theorem zParitySlot_step {nq : Nat} (anc : Fin nq) (slot : ScheduledPauli nq)
    (E : Fin nq -> Pauli) (b : Bool) (es : ErrorState nq)
    (hne : slot.qubit ≠ anc)
    (hdata : ∀ q : Fin nq, q ≠ anc -> es.paulis q = E q)
    (hanc : es.paulis anc = xOfBool b) :
    let es' := propagateCircuit (eraseFaults (zParitySlot anc slot)) es
    es'.paulis anc = xOfBool (xor b (anticommute slot.kind.toPauli (E slot.qubit))) ∧
      ∀ q : Fin nq, q ≠ anc -> es'.paulis q = E q := by
  cases slot with
  | mk kind qubit =>
    have hne' : anc ≠ qubit := fun h => hne h.symm
    cases kind
    · constructor
      · simp [zParitySlot, hadamard, cnot, hne, hne', propagateCircuit, propagateGate,
          hanc, hdata qubit hne]
        cases b <;> cases E qubit <;> rfl
      · intro q hqanc
        by_cases hq : q = qubit
        · subst q
          simp [zParitySlot, hadamard, cnot, hne, hne', propagateCircuit, propagateGate,
            hanc, hdata qubit hne]
        · simp [zParitySlot, hadamard, cnot, hne, hne', propagateCircuit, propagateGate,
            hq, hqanc, hdata q hqanc, hanc]
    · constructor
      · simp [zParitySlot, cnot, hne, propagateCircuit, propagateGate,
          hanc, hdata qubit hne]
        cases b <;> cases E qubit <;> rfl
      · intro q hqanc
        by_cases hq : q = qubit
        · subst q
          simp [zParitySlot, cnot, hne, propagateCircuit, propagateGate,
            hanc, hdata qubit hne]
        · simp [zParitySlot, cnot, hne, propagateCircuit, propagateGate,
            hq, hqanc, hdata q hqanc, hanc]

theorem zParitySlotsCircuit_chain {nq : Nat} (anc : Fin nq)
    (slots : List (ScheduledPauli nq)) (E : Fin nq -> Pauli)
    (b : Bool) (es : ErrorState nq)
    (hne : ∀ slot, slot ∈ slots -> slot.qubit ≠ anc)
    (hdata : ∀ q : Fin nq, q ≠ anc -> es.paulis q = E q)
    (hanc : es.paulis anc = xOfBool b) :
    let es' := propagateCircuit (eraseFaults (zParitySlotsCircuit anc slots)) es
    es'.paulis anc = xOfBool (scheduleParityList slots E b) ∧
      ∀ q : Fin nq, q ≠ anc -> es'.paulis q = E q := by
  induction slots generalizing b es with
  | nil =>
      constructor
      · simpa [zParitySlotsCircuit, scheduleParityList, propagateCircuit] using hanc
      · intro q hq
        simpa [zParitySlotsCircuit, propagateCircuit] using hdata q hq
  | cons slot rest ih =>
      have hslot : slot.qubit ≠ anc := hne slot (by simp)
      have hrest : ∀ slot', slot' ∈ rest -> slot'.qubit ≠ anc := by
        intro slot' hmem
        exact hne slot' (by simp [hmem])
      let es1 := propagateCircuit (eraseFaults (zParitySlot anc slot)) es
      have hstep := zParitySlot_step anc slot E b es hslot hdata hanc
      have hih := ih (xor b (anticommute slot.kind.toPauli (E slot.qubit))) es1
        hrest hstep.2 hstep.1
      simpa [zParitySlotsCircuit, scheduleParityList, es1, eraseFaults_append,
        QHL.Target.propagateCircuit_append] using hih

theorem zParitySlot_preserves_readout {nq : Nat} (anc : Fin nq)
    (slot : ScheduledPauli nq) (es : ErrorState nq) :
    let es' := propagateCircuit (eraseFaults (zParitySlot anc slot)) es
    es'.detectors = es.detectors ∧ es'.detectorCursor = es.detectorCursor := by
  cases slot with
  | mk kind qubit =>
    cases kind
    · by_cases h : qubit = anc
      · simp [zParitySlot, hadamard, cnot, h, propagateCircuit, propagateGate]
      · simp [zParitySlot, hadamard, cnot, h, propagateCircuit, propagateGate]
    · by_cases h : qubit = anc
      · simp [zParitySlot, cnot, h, propagateCircuit]
      · simp [zParitySlot, cnot, h, propagateCircuit, propagateGate]

theorem zParitySlotsCircuit_preserves_readout {nq : Nat} (anc : Fin nq)
    (slots : List (ScheduledPauli nq)) (es : ErrorState nq) :
    let es' := propagateCircuit (eraseFaults (zParitySlotsCircuit anc slots)) es
    es'.detectors = es.detectors ∧ es'.detectorCursor = es.detectorCursor := by
  induction slots generalizing es with
  | nil =>
      simp [zParitySlotsCircuit, propagateCircuit]
  | cons slot rest ih =>
      let es1 := propagateCircuit (eraseFaults (zParitySlot anc slot)) es
      have hslot := zParitySlot_preserves_readout anc slot es
      have hrest := ih es1
      constructor
      · simpa [zParitySlotsCircuit, es1, eraseFaults_append,
          QHL.Target.propagateCircuit_append, hslot.1] using hrest.1
      · simpa [zParitySlotsCircuit, es1, eraseFaults_append,
          QHL.Target.propagateCircuit_append, hslot.2] using hrest.2

theorem prep0_state_for_chain {nq : Nat} (anc : Fin nq) (es : ErrorState nq) :
    let es' := propagateCircuit (eraseFaults (prep0 anc)) es
    es'.paulis anc = xOfBool false ∧
      (∀ q : Fin nq, q ≠ anc -> es'.paulis q = es.paulis q) ∧
      es'.detectors = es.detectors ∧
      es'.detectorCursor = es.detectorCursor := by
  constructor
  · simp [prep0, eraseFaults, propagateCircuit, propagateGate, xOfBool]
  constructor
  · intro q hq
    simp [prep0, eraseFaults, propagateCircuit, propagateGate, hq]
  constructor <;> simp [prep0, eraseFaults, propagateCircuit, propagateGate]

theorem prepP_state_for_chain {nq : Nat} (anc : Fin nq) (es : ErrorState nq) :
    let es' := propagateCircuit (eraseFaults (prepP anc)) es
    es'.paulis anc = xOfBool false ∧
      (∀ q : Fin nq, q ≠ anc -> es'.paulis q = es.paulis q) ∧
      es'.detectors = es.detectors ∧
      es'.detectorCursor = es.detectorCursor := by
  constructor
  · simp [prepP, eraseFaults, propagateCircuit, propagateGate, xOfBool]
  constructor
  · intro q hq
    simp [prepP, eraseFaults, propagateCircuit, propagateGate, hq]
  constructor <;> simp [prepP, eraseFaults, propagateCircuit, propagateGate]

theorem cleanCnot_preserves_all {nq : Nat} (c t : Fin nq) (es : ErrorState nq)
    (hc : es.paulis c = Pauli.I) (ht : es.paulis t = Pauli.I) :
    let es' := propagateCircuit (eraseFaults (cnot c t)) es
    es'.paulis = es.paulis ∧ es'.detectors = es.detectors ∧
      es'.detectorCursor = es.detectorCursor := by
  by_cases h : c = t
  · subst t
    simp [cnot, propagateCircuit]
  · constructor
    · funext q
      by_cases hqt : q = t
      · subst q
        simp [cnot, h, eraseFaults, propagateCircuit, propagateGate, hc, ht, xPart]
      · by_cases hqc : q = c
        · subst q
          simp [cnot, h, eraseFaults, propagateCircuit, propagateGate, hc, ht, zPart]
        · simp [cnot, h, eraseFaults, propagateCircuit, propagateGate, hqt, hqc]
    constructor <;> simp [cnot, h, eraseFaults, propagateCircuit, propagateGate]

theorem cleanCnotPairs_preserves_all {nq : Nat} (pairs : List (Fin nq × Fin nq))
    (es : ErrorState nq)
    (hclean : ∀ pair, pair ∈ pairs -> es.paulis pair.1 = Pauli.I ∧
      es.paulis pair.2 = Pauli.I) :
    let es' :=
      propagateCircuit (eraseFaults ((pairs.map (fun pair => cnot pair.1 pair.2)).flatten))
        es
    es'.paulis = es.paulis ∧ es'.detectors = es.detectors ∧
      es'.detectorCursor = es.detectorCursor := by
  induction pairs generalizing es with
  | nil =>
      simp [propagateCircuit]
  | cons pair rest ih =>
      let es1 := propagateCircuit (eraseFaults (cnot pair.1 pair.2)) es
      have hstep :=
        cleanCnot_preserves_all pair.1 pair.2 es
          (hclean pair (by simp)).1 (hclean pair (by simp)).2
      have hrestClean :
          ∀ pair', pair' ∈ rest -> es1.paulis pair'.1 = Pauli.I ∧
            es1.paulis pair'.2 = Pauli.I := by
        intro pair' hmem
        have hp := hclean pair' (by simp [hmem])
        constructor
        · rw [hstep.1]
          exact hp.1
        · rw [hstep.1]
          exact hp.2
      have htail := ih es1 hrestClean
      have hcompiled :
          propagateCircuit
              (eraseFaults
                (((pair :: rest).map (fun pair => cnot pair.1 pair.2)).flatten))
              es =
            propagateCircuit
              (eraseFaults ((rest.map (fun pair => cnot pair.1 pair.2)).flatten)) es1 := by
        simp [es1, eraseFaults_append, QHL.Target.propagateCircuit_append]
      constructor
      · rw [hcompiled]
        exact htail.1.trans hstep.1
      constructor
      · rw [hcompiled]
        exact htail.2.1.trans hstep.2.1
      · rw [hcompiled]
        exact htail.2.2.trans hstep.2.2

theorem orderedCatPrepZ_clean_preserves_all {nq : Nat} (cat : List (Fin nq))
    (es : ErrorState nq)
    (hclean : ∀ q, q ∈ cat -> es.paulis q = Pauli.I) :
    let es' := propagateCircuit (eraseFaults (orderedCatPrepZ cat)) es
    es'.paulis = es.paulis ∧ es'.detectors = es.detectors ∧
      es'.detectorCursor = es.detectorCursor := by
  cases cat with
  | nil =>
      simp [orderedCatPrepZ, propagateCircuit]
  | cons c0 rest =>
      let esPrep := propagateCircuit (eraseFaults (prep0 c0)) es
      have hprep := prep0_state_for_chain c0 es
      have hprepPaulis : esPrep.paulis = es.paulis := by
        funext q
        by_cases hq : q = c0
        · subst q
          have hc0 : es.paulis c0 = Pauli.I := hclean c0 (by simp)
          simpa [esPrep, xOfBool, hc0] using hprep.1
        · simpa [esPrep] using hprep.2.1 q hq
      have hpairClean :
          ∀ pair, pair ∈ List.zip (c0 :: rest) rest ->
            esPrep.paulis pair.1 = Pauli.I ∧ esPrep.paulis pair.2 = Pauli.I := by
        intro pair hmem
        have hleft : pair.1 ∈ c0 :: rest := (List.of_mem_zip hmem).1
        have hright : pair.2 ∈ rest := (List.of_mem_zip hmem).2
        constructor
        · rw [hprepPaulis]
          exact hclean pair.1 hleft
        · rw [hprepPaulis]
          exact hclean pair.2 (by simp [hright])
      have htail := cleanCnotPairs_preserves_all (List.zip (c0 :: rest) rest) esPrep hpairClean
      have hcompiled :
          propagateCircuit (eraseFaults (orderedCatPrepZ (c0 :: rest))) es =
            propagateCircuit
              (eraseFaults (((List.zip (c0 :: rest) rest).map
                (fun pair => cnot pair.1 pair.2)).flatten)) esPrep := by
        simp [orderedCatPrepZ, esPrep, eraseFaults_append,
          QHL.Target.propagateCircuit_append]
      constructor
      · rw [hcompiled]
        exact htail.1.trans hprepPaulis
      constructor
      · rw [hcompiled]
        exact htail.2.1.trans hprep.2.2.1
      · rw [hcompiled]
        exact htail.2.2.trans hprep.2.2.2

theorem hadamard_clean_preserves_all {nq : Nat} (q : Fin nq) (es : ErrorState nq)
    (hq : es.paulis q = Pauli.I) :
    let es' := propagateCircuit (eraseFaults (hadamard q)) es
    es'.paulis = es.paulis ∧ es'.detectors = es.detectors ∧
      es'.detectorCursor = es.detectorCursor := by
  constructor
  · funext r
    by_cases hr : r = q
    · subst r
      simp [hadamard, eraseFaults, propagateCircuit, propagateGate, hq]
    · simp [hadamard, eraseFaults, propagateCircuit, propagateGate, hr]
  constructor <;> simp [hadamard, eraseFaults, propagateCircuit, propagateGate]

theorem flagMeasZ_clean_cursor {nq : Nat} (q : Fin nq) (es : ErrorState nq)
    (start : Nat) (hq : es.paulis q = Pauli.I) (hcursor : es.detectorCursor = start) :
    let es' := propagateCircuit (eraseFaults (flagMeasZ q)) es
    es'.detectors start = false ∧ es'.detectorCursor = start + 1 ∧
      es'.paulis = es.paulis := by
  constructor
  · simp [flagMeasZ, eraseFaults, propagateCircuit, propagateGate, hq, hcursor]
  constructor
  · simp [flagMeasZ, eraseFaults, propagateCircuit, propagateGate, hcursor]
  · funext r
    simp [flagMeasZ, eraseFaults, propagateCircuit, propagateGate]

theorem cleanFlagCnot_preserves_anc {nq : Nat} (flag anc : Fin nq) (es : ErrorState nq)
    (b : Bool) (hflagAnc : flag ≠ anc)
    (hflag : es.paulis flag = xOfBool false)
    (hanc : es.paulis anc = xOfBool b) :
    let es' := propagateCircuit (eraseFaults (cnot flag anc)) es
    es'.paulis anc = xOfBool b ∧
      es'.paulis flag = xOfBool false ∧
      (∀ q : Fin nq, q ≠ anc -> q ≠ flag -> es'.paulis q = es.paulis q) ∧
      es'.detectors = es.detectors ∧
      es'.detectorCursor = es.detectorCursor := by
  constructor
  · simp [cnot, hflagAnc, eraseFaults, propagateCircuit, propagateGate,
      hflag, hanc]
  constructor
  · simp [cnot, hflagAnc, eraseFaults, propagateCircuit, propagateGate,
      hflag, hanc]
  constructor
  · intro q hqAnc hqFlag
    simp [cnot, hflagAnc, eraseFaults, propagateCircuit, propagateGate,
      hqAnc, hqFlag, hflag, hanc]
  constructor <;>
    simp [cnot, hflagAnc, eraseFaults, propagateCircuit, propagateGate]

theorem flagMeasZ_detector_zero {nq : Nat} (anc : Fin nq) (es : ErrorState nq)
    (hcursor : es.detectorCursor = 0) :
    (propagateCircuit (eraseFaults (flagMeasZ anc)) es).detectors 0 =
      hasXComp (es.paulis anc) := by
  simp [flagMeasZ, eraseFaults, propagateCircuit, propagateGate, hcursor]

theorem rawMeasZ_detector_cursor {nq : Nat} (anc : Fin nq) (es : ErrorState nq) :
    let es' := propagateCircuit (eraseFaults (rawMeasZ anc)) es
    es'.detectors es.detectorCursor = hasXComp (es.paulis anc) ∧
      es'.detectorCursor = es.detectorCursor + 1 ∧
      es'.paulis = es.paulis := by
  constructor
  · simp [rawMeasZ, eraseFaults, propagateCircuit, propagateGate]
  constructor
  · simp [rawMeasZ, eraseFaults, propagateCircuit, propagateGate]
  · funext q
    simp [rawMeasZ, eraseFaults, propagateCircuit, propagateGate]

theorem knillSlot_step {nq : Nat} (slot : ScheduledPauli nq) (anc : Fin nq)
    (es : ErrorState nq) (hne : slot.qubit ≠ anc) :
    let es' := propagateCircuit (eraseFaults (knillSlot slot anc)) es
    es'.detectors es.detectorCursor =
        anticommute slot.kind.toPauli (es.paulis slot.qubit) ∧
      es'.detectorCursor = es.detectorCursor + 1 ∧
      (∀ q : Fin nq, q ≠ anc -> es'.paulis q = es.paulis q) ∧
      (∀ j : Nat, j < es.detectorCursor -> es'.detectors j = es.detectors j) := by
  let esPrep := propagateCircuit (eraseFaults (prep0 anc)) es
  let curE : Fin nq -> Pauli := fun q => esPrep.paulis q
  let esSlots := propagateCircuit (eraseFaults (zParitySlot anc slot)) esPrep
  have hprep := prep0_state_for_chain anc es
  have hdata : ∀ q : Fin nq, q ≠ anc -> esPrep.paulis q = curE q := by
    intro q _hq
    rfl
  have hanc : esPrep.paulis anc = xOfBool false := by
    simpa [esPrep] using hprep.1
  have hslotCur : curE slot.qubit = es.paulis slot.qubit := by
    simpa [curE, esPrep] using hprep.2.1 slot.qubit hne
  have hstep := zParitySlot_step anc slot curE false esPrep hne hdata hanc
  have hraw := rawMeasZ_detector_cursor anc esSlots
  have hcompiled :
      propagateCircuit (eraseFaults (knillSlot slot anc)) es =
        propagateCircuit (eraseFaults (rawMeasZ anc)) esSlots := by
    simp [knillSlot, esPrep, esSlots, eraseFaults_append,
      QHL.Target.propagateCircuit_append]
  constructor
  · rw [hcompiled]
    calc
      (propagateCircuit (eraseFaults (rawMeasZ anc)) esSlots).detectors es.detectorCursor
          = (propagateCircuit (eraseFaults (rawMeasZ anc)) esSlots).detectors
              esSlots.detectorCursor := by
            have hread := zParitySlot_preserves_readout anc slot esPrep
            have hcurPrep : esPrep.detectorCursor = es.detectorCursor := by
              simpa [esPrep] using hprep.2.2.2
            have hcurSlots : esSlots.detectorCursor = es.detectorCursor := by
              calc
                esSlots.detectorCursor = esPrep.detectorCursor := by
                  simpa [esSlots] using hread.2
                _ = es.detectorCursor := hcurPrep
            rw [hcurSlots]
      _ = hasXComp (esSlots.paulis anc) := hraw.1
      _ = hasXComp (xOfBool (anticommute slot.kind.toPauli (curE slot.qubit))) := by
            rw [show esSlots.paulis anc =
                xOfBool (anticommute slot.kind.toPauli (curE slot.qubit)) by
              simpa [esSlots, scheduleParityList, xor] using hstep.1]
      _ = anticommute slot.kind.toPauli (curE slot.qubit) := by simp
      _ = anticommute slot.kind.toPauli (es.paulis slot.qubit) := by rw [hslotCur]
  constructor
  · rw [hcompiled]
    have hread := zParitySlot_preserves_readout anc slot esPrep
    have hcurPrep : esPrep.detectorCursor = es.detectorCursor := by
      simpa [esPrep] using hprep.2.2.2
    have hcurSlots : esSlots.detectorCursor = es.detectorCursor := by
      calc
        esSlots.detectorCursor = esPrep.detectorCursor := by
          simpa [esSlots] using hread.2
        _ = es.detectorCursor := hcurPrep
    calc
      (propagateCircuit (eraseFaults (rawMeasZ anc)) esSlots).detectorCursor
          = esSlots.detectorCursor + 1 := hraw.2.1
      _ = es.detectorCursor + 1 := by rw [hcurSlots]
  constructor
  · intro q hq
    rw [hcompiled]
    have hrawPaulis :
        (propagateCircuit (eraseFaults (rawMeasZ anc)) esSlots).paulis = esSlots.paulis :=
      hraw.2.2
    rw [hrawPaulis]
    have hslotsQ : esSlots.paulis q = curE q := by
      simpa [esSlots] using hstep.2 q hq
    have hprepQ : curE q = es.paulis q := by
      simpa [curE, esPrep] using hprep.2.1 q hq
    exact hslotsQ.trans hprepQ
  · intro j hj
    rw [hcompiled]
    have hread := zParitySlot_preserves_readout anc slot esPrep
    have hcurPrep : esPrep.detectorCursor = es.detectorCursor := by
      simpa [esPrep] using hprep.2.2.2
    have hcurSlots : esSlots.detectorCursor = es.detectorCursor := by
      calc
        esSlots.detectorCursor = esPrep.detectorCursor := by
          simpa [esSlots] using hread.2
        _ = es.detectorCursor := hcurPrep
    have hjne : j ≠ esSlots.detectorCursor := by
      intro h
      rw [hcurSlots] at h
      omega
    have hrawDet :
        (propagateCircuit (eraseFaults (rawMeasZ anc)) esSlots).detectors j =
          esSlots.detectors j := by
      simp [rawMeasZ, eraseFaults, propagateCircuit, propagateGate, hjne]
    have hslotsDet : esSlots.detectors j = esPrep.detectors j := by
      simpa [esSlots] using congrFun hread.1 j
    have hprepDet : esPrep.detectors j = es.detectors j := by
      simpa [esPrep] using congrFun hprep.2.2.1 j
    exact hrawDet.trans (hslotsDet.trans hprepDet)

theorem knillPairsCircuit_chain {nq : Nat}
    (pairs : List (ScheduledPauli nq × Fin nq)) (E : Fin nq -> Pauli)
    (init : Bool) (es : ErrorState nq) (start : Nat)
    (hcursor : es.detectorCursor = start)
    (hdata : ∀ pair, pair ∈ pairs -> es.paulis pair.1.qubit = E pair.1.qubit)
    (hself : ∀ pair, pair ∈ pairs -> pair.1.qubit ≠ pair.2)
    (hslot_ne_anc :
      ∀ slotPair, slotPair ∈ pairs ->
        ∀ ancPair, ancPair ∈ pairs -> slotPair.1.qubit ≠ ancPair.2) :
    let es' := propagateCircuit (eraseFaults (knillPairsCircuit pairs)) es
    detectorXorFromAcc start pairs.length es' init =
        scheduleParityList (pairs.map Prod.fst) E init ∧
      es'.detectorCursor = start + pairs.length ∧
      (∀ j : Nat, j < start -> es'.detectors j = es.detectors j) ∧
      (∀ q : Fin nq,
        (∀ pair, pair ∈ pairs -> q ≠ pair.2) -> es'.paulis q = es.paulis q) := by
  induction pairs generalizing init es start with
  | nil =>
      constructor
      · rfl
      constructor
      · simpa [knillPairsCircuit, propagateCircuit] using hcursor
      constructor
      · intro j _hj
        rfl
      · intro q _hq
        rfl
  | cons pair rest ih =>
      let bit := anticommute pair.1.kind.toPauli (E pair.1.qubit)
      let es1 := propagateCircuit (eraseFaults (knillSlot pair.1 pair.2)) es
      let esFinal := propagateCircuit (eraseFaults (knillPairsCircuit rest)) es1
      have hpairMem : pair ∈ pair :: rest := by simp
      have hpairSelf : pair.1.qubit ≠ pair.2 := hself pair hpairMem
      have hstep := knillSlot_step pair.1 pair.2 es hpairSelf
      have hbit : es1.detectors start = bit := by
        have hb := hstep.1
        rw [hcursor] at hb
        have hd := hdata pair hpairMem
        rw [hd] at hb
        simpa [bit, es1] using hb
      have htailCursor : es1.detectorCursor = start + 1 := by
        calc
          es1.detectorCursor = es.detectorCursor + 1 := by
            simpa [es1] using hstep.2.1
          _ = start + 1 := by rw [hcursor]
      have htailData :
          ∀ tailPair, tailPair ∈ rest ->
            es1.paulis tailPair.1.qubit = E tailPair.1.qubit := by
        intro tailPair htailMem
        have hneq : tailPair.1.qubit ≠ pair.2 :=
          hslot_ne_anc tailPair (by simp [htailMem]) pair hpairMem
        have hpres := hstep.2.2.1 tailPair.1.qubit hneq
        have hdat := hdata tailPair (by simp [htailMem])
        simpa [es1] using hpres.trans hdat
      have htailSelf :
          ∀ tailPair, tailPair ∈ rest -> tailPair.1.qubit ≠ tailPair.2 := by
        intro tailPair htailMem
        exact hself tailPair (by simp [htailMem])
      have htailSlotAnc :
          ∀ slotPair, slotPair ∈ rest ->
            ∀ ancPair, ancPair ∈ rest -> slotPair.1.qubit ≠ ancPair.2 := by
        intro slotPair hslotMem ancPair hancMem
        exact hslot_ne_anc slotPair (by simp [hslotMem]) ancPair (by simp [hancMem])
      have htail :=
        ih (xor init bit) es1 (start + 1) htailCursor htailData
          htailSelf htailSlotAnc
      have hcompiled :
          propagateCircuit (eraseFaults (knillPairsCircuit (pair :: rest))) es =
            esFinal := by
        simp [knillPairsCircuit, es1, esFinal, eraseFaults_append,
          QHL.Target.propagateCircuit_append]
      constructor
      · rw [hcompiled]
        change detectorXorFromAcc start (rest.length + 1) esFinal init =
          scheduleParityList (pair.1 :: rest.map Prod.fst) E init
        calc
          detectorXorFromAcc start (rest.length + 1) esFinal init =
              detectorXorFromAcc (start + 1) rest.length esFinal
                (xor init (esFinal.detectors start)) := rfl
          _ = detectorXorFromAcc (start + 1) rest.length esFinal
                (xor init (es1.detectors start)) := by
                rw [htail.2.2.1 start (by omega)]
          _ = detectorXorFromAcc (start + 1) rest.length esFinal (xor init bit) := by
                rw [hbit]
          _ = scheduleParityList (rest.map Prod.fst) E (xor init bit) := htail.1
          _ = scheduleParityList (pair.1 :: rest.map Prod.fst) E init := by
                simp [scheduleParityList, bit]
      constructor
      · rw [hcompiled]
        calc
          esFinal.detectorCursor = start + 1 + rest.length := htail.2.1
          _ = start + (rest.length + 1) := by omega
      constructor
      · intro j hj
        rw [hcompiled]
        calc
          esFinal.detectors j = es1.detectors j := htail.2.2.1 j (by omega)
          _ = es.detectors j := hstep.2.2.2 j (by rwa [hcursor])
      · intro q hq
        rw [hcompiled]
        have htailPres : esFinal.paulis q = es1.paulis q := by
          exact htail.2.2.2 q (by
            intro tailPair htailMem
            exact hq tailPair (by simp [htailMem]))
        have hstepPres : es1.paulis q = es.paulis q := by
          exact hstep.2.2.1 q (hq pair hpairMem)
        exact htailPres.trans hstepPres

theorem shorCouplingSlot_step {nq : Nat} (slot : ScheduledPauli nq) (cat : Fin nq)
    (es : ErrorState nq) (hne : slot.qubit ≠ cat)
    (hcat : es.paulis cat = xOfBool false) :
    let es' := propagateCircuit (eraseFaults (shorCouplingSlot slot cat)) es
    es'.paulis cat = xOfBool (anticommute slot.kind.toPauli (es.paulis slot.qubit)) ∧
      (∀ q : Fin nq, q ≠ cat -> es'.paulis q = es.paulis q) ∧
      es'.detectors = es.detectors ∧ es'.detectorCursor = es.detectorCursor := by
  have hstep :=
    zParitySlot_step cat slot (fun q => es.paulis q) false es hne (fun q _ => rfl) hcat
  have hread := zParitySlot_preserves_readout cat slot es
  constructor
  · simpa [shorCouplingSlot, zParitySlot, xor] using hstep.1
  constructor
  · intro q hq
    simpa [shorCouplingSlot, zParitySlot] using hstep.2 q hq
  constructor
  · simpa [shorCouplingSlot, zParitySlot] using hread.1
  · simpa [shorCouplingSlot, zParitySlot] using hread.2

theorem shorCouplingPairsCircuit_chain {nq : Nat}
    (pairs : List (ScheduledPauli nq × Fin nq)) (E : Fin nq -> Pauli)
    (es : ErrorState nq)
    (hnodup : pairs.Nodup)
    (hdata : ∀ pair, pair ∈ pairs -> es.paulis pair.1.qubit = E pair.1.qubit)
    (hcat : ∀ pair, pair ∈ pairs -> es.paulis pair.2 = xOfBool false)
    (hself : ∀ pair, pair ∈ pairs -> pair.1.qubit ≠ pair.2)
    (hslot_ne_cat :
      ∀ slotPair, slotPair ∈ pairs ->
        ∀ catPair, catPair ∈ pairs -> slotPair.1.qubit ≠ catPair.2)
    (hcat_ne :
      ∀ pairA, pairA ∈ pairs ->
        ∀ pairB, pairB ∈ pairs -> pairA ≠ pairB -> pairA.2 ≠ pairB.2) :
    let es' := propagateCircuit (eraseFaults (shorCouplingPairsCircuit pairs)) es
    (∀ pair, pair ∈ pairs ->
      es'.paulis pair.2 =
        xOfBool (anticommute pair.1.kind.toPauli (E pair.1.qubit))) ∧
      (∀ q : Fin nq,
        (∀ pair, pair ∈ pairs -> q ≠ pair.2) -> es'.paulis q = es.paulis q) ∧
      es'.detectors = es.detectors ∧ es'.detectorCursor = es.detectorCursor := by
  induction pairs generalizing es with
  | nil =>
      simp [shorCouplingPairsCircuit, propagateCircuit]
  | cons pair rest ih =>
      let es1 := propagateCircuit (eraseFaults (shorCouplingSlot pair.1 pair.2)) es
      let esFinal := propagateCircuit (eraseFaults (shorCouplingPairsCircuit rest)) es1
      have hpairMem : pair ∈ pair :: rest := by simp
      have hpairSelf : pair.1.qubit ≠ pair.2 := hself pair hpairMem
      have hpairCat : es.paulis pair.2 = xOfBool false := hcat pair hpairMem
      have hstep := shorCouplingSlot_step pair.1 pair.2 es hpairSelf hpairCat
      have hpair_not_rest : pair ∉ rest := by
        have h := hnodup
        simp at h
        exact h.1
      have hrest_nodup : rest.Nodup := by
        have h := hnodup
        simp at h
        exact h.2
      have htailData :
          ∀ tailPair, tailPair ∈ rest ->
            es1.paulis tailPair.1.qubit = E tailPair.1.qubit := by
        intro tailPair htailMem
        have hneq : tailPair.1.qubit ≠ pair.2 :=
          hslot_ne_cat tailPair (by simp [htailMem]) pair hpairMem
        have hpres := hstep.2.1 tailPair.1.qubit hneq
        have hdat := hdata tailPair (by simp [htailMem])
        simpa [es1] using hpres.trans hdat
      have htailCat :
          ∀ tailPair, tailPair ∈ rest -> es1.paulis tailPair.2 = xOfBool false := by
        intro tailPair htailMem
        have htail_ne_pair : tailPair ≠ pair := by
          intro h
          exact hpair_not_rest (by simpa [h] using htailMem)
        have hneq : tailPair.2 ≠ pair.2 :=
          hcat_ne tailPair (by simp [htailMem]) pair hpairMem htail_ne_pair
        have hpres := hstep.2.1 tailPair.2 hneq
        have hcatTail := hcat tailPair (by simp [htailMem])
        simpa [es1] using hpres.trans hcatTail
      have htailSelf :
          ∀ tailPair, tailPair ∈ rest -> tailPair.1.qubit ≠ tailPair.2 := by
        intro tailPair htailMem
        exact hself tailPair (by simp [htailMem])
      have htailSlotCat :
          ∀ slotPair, slotPair ∈ rest ->
            ∀ catPair, catPair ∈ rest -> slotPair.1.qubit ≠ catPair.2 := by
        intro slotPair hslotMem catPair hcatMem
        exact hslot_ne_cat slotPair (by simp [hslotMem]) catPair (by simp [hcatMem])
      have htailCatNe :
          ∀ pairA, pairA ∈ rest ->
            ∀ pairB, pairB ∈ rest -> pairA ≠ pairB -> pairA.2 ≠ pairB.2 := by
        intro pairA hAMem pairB hBMem hne
        exact hcat_ne pairA (by simp [hAMem]) pairB (by simp [hBMem]) hne
      have htail :=
        ih es1 hrest_nodup htailData htailCat htailSelf htailSlotCat htailCatNe
      have hcompiled :
          propagateCircuit (eraseFaults (shorCouplingPairsCircuit (pair :: rest))) es =
            esFinal := by
        simp [shorCouplingPairsCircuit, es1, esFinal, eraseFaults_append,
          QHL.Target.propagateCircuit_append]
      constructor
      · intro query hqueryMem
        rw [hcompiled]
        by_cases hqueryEq : query = pair
        · subst query
          have hpres : esFinal.paulis pair.2 = es1.paulis pair.2 := by
            exact htail.2.1 pair.2 (by
              intro tailPair htailMem
              have htail_ne_pair : tailPair ≠ pair := by
                intro h
                exact hpair_not_rest (by simpa [h] using htailMem)
              exact hcat_ne pair hpairMem tailPair (by simp [htailMem])
                (fun h => htail_ne_pair h.symm))
          have hbit : es1.paulis pair.2 =
              xOfBool (anticommute pair.1.kind.toPauli (E pair.1.qubit)) := by
            have hs := hstep.1
            have hd := hdata pair hpairMem
            rw [hd] at hs
            simpa [es1] using hs
          exact hpres.trans hbit
        · have htailMem : query ∈ rest := by
            simpa [hqueryEq] using hqueryMem
          exact htail.1 query htailMem
      constructor
      · intro q hq
        rw [hcompiled]
        have htailPres : esFinal.paulis q = es1.paulis q := by
          exact htail.2.1 q (by
            intro tailPair htailMem
            exact hq tailPair (by simp [htailMem]))
        have hstepPres : es1.paulis q = es.paulis q := by
          exact hstep.2.1 q (hq pair hpairMem)
        exact htailPres.trans hstepPres
      constructor
      · rw [hcompiled]
        exact htail.2.2.1.trans hstep.2.2.1
      · rw [hcompiled]
        exact htail.2.2.2.trans hstep.2.2.2

theorem rawMeasZPairsCircuit_chain {nq : Nat}
    (pairs : List (ScheduledPauli nq × Fin nq)) (E : Fin nq -> Pauli)
    (init : Bool) (es : ErrorState nq) (start : Nat)
    (hcursor : es.detectorCursor = start)
    (hbits :
      ∀ pair, pair ∈ pairs ->
        es.paulis pair.2 =
          xOfBool (anticommute pair.1.kind.toPauli (E pair.1.qubit))) :
    let es' := propagateCircuit (eraseFaults (rawMeasZPairsCircuit pairs)) es
    detectorXorFromAcc start pairs.length es' init =
        scheduleParityList (pairs.map Prod.fst) E init ∧
      es'.detectorCursor = start + pairs.length ∧
      (∀ j : Nat, j < start -> es'.detectors j = es.detectors j) ∧
      es'.paulis = es.paulis := by
  induction pairs generalizing init es start with
  | nil =>
      constructor
      · rfl
      constructor
      · simpa [rawMeasZPairsCircuit, propagateCircuit] using hcursor
      constructor
      · intro j _hj
        rfl
      · rfl
  | cons pair rest ih =>
      let es1 := propagateCircuit (eraseFaults (rawMeasZ pair.2)) es
      let esFinal := propagateCircuit (eraseFaults (rawMeasZPairsCircuit rest)) es1
      have hpairMem : pair ∈ pair :: rest := by simp
      have hraw := rawMeasZ_detector_cursor pair.2 es
      have hbit : es1.detectors start =
          anticommute pair.1.kind.toPauli (E pair.1.qubit) := by
        have hb := hraw.1
        rw [hcursor] at hb
        have hp := hbits pair hpairMem
        rw [hp] at hb
        simpa [es1] using hb
      have htailCursor : es1.detectorCursor = start + 1 := by
        calc
          es1.detectorCursor = es.detectorCursor + 1 := by
            simpa [es1] using hraw.2.1
          _ = start + 1 := by rw [hcursor]
      have htailBits :
          ∀ tailPair, tailPair ∈ rest ->
            es1.paulis tailPair.2 =
              xOfBool (anticommute tailPair.1.kind.toPauli (E tailPair.1.qubit)) := by
        intro tailPair htailMem
        have hp := hbits tailPair (by simp [htailMem])
        rw [hraw.2.2]
        exact hp
      have htail := ih (xor init (anticommute pair.1.kind.toPauli (E pair.1.qubit)))
        es1 (start + 1) htailCursor htailBits
      have hcompiled :
          propagateCircuit (eraseFaults (rawMeasZPairsCircuit (pair :: rest))) es =
            esFinal := by
        simp [rawMeasZPairsCircuit, es1, esFinal, eraseFaults_append,
          QHL.Target.propagateCircuit_append]
      constructor
      · rw [hcompiled]
        change detectorXorFromAcc start (rest.length + 1) esFinal init =
          scheduleParityList (pair.1 :: rest.map Prod.fst) E init
        calc
          detectorXorFromAcc start (rest.length + 1) esFinal init =
              detectorXorFromAcc (start + 1) rest.length esFinal
                (xor init (esFinal.detectors start)) := rfl
          _ = detectorXorFromAcc (start + 1) rest.length esFinal
                (xor init (es1.detectors start)) := by
                rw [htail.2.2.1 start (by omega)]
          _ = detectorXorFromAcc (start + 1) rest.length esFinal
                (xor init (anticommute pair.1.kind.toPauli (E pair.1.qubit))) := by
                rw [hbit]
          _ = scheduleParityList (rest.map Prod.fst) E
                (xor init (anticommute pair.1.kind.toPauli (E pair.1.qubit))) := htail.1
          _ = scheduleParityList (pair.1 :: rest.map Prod.fst) E init := by
                simp [scheduleParityList]
      constructor
      · rw [hcompiled]
        calc
          esFinal.detectorCursor = start + 1 + rest.length := htail.2.1
          _ = start + (rest.length + 1) := by omega
      constructor
      · intro j hj
        rw [hcompiled]
        calc
          esFinal.detectors j = es1.detectors j := htail.2.2.1 j (by omega)
          _ = es.detectors j := by
            have hjne : j ≠ es.detectorCursor := by
              intro h
              rw [hcursor] at h
              omega
            simp [es1, rawMeasZ, eraseFaults, propagateCircuit, propagateGate, hjne]
      · rw [hcompiled]
        exact htail.2.2.2.trans hraw.2.2

theorem flagTail_preserves_detector_zero {nq : Nat} (flag : Fin nq) (es : ErrorState nq)
    (hcursor : es.detectorCursor = 1) :
    (propagateCircuit (eraseFaults (hadamard flag ++ flagMeasZ flag)) es).detectors 0 =
      es.detectors 0 := by
  simp [hadamard, flagMeasZ, eraseFaults, propagateCircuit, propagateGate, hcursor]

def GadgetDetectorCorrect {n : Nat} (scheme : Scheme) (sigma : RuleSchedule n) :
    Prop :=
  ∀ E : Fin n -> Pauli,
    gadgetDetectorBit scheme sigma
        (propagateCircuit (eraseFaults (compileFreshGadget scheme sigma))
          (dataInputState (k := helperCount scheme sigma) E)) =
      scheduleParity sigma E

theorem compileFreshGadget_NZ_correct {n : Nat} (sigma : RuleSchedule n) :
    GadgetDetectorCorrect .NZ sigma := by
  intro E
  let anc : Fin (n + 1) := freshHelperQ n 1 ⟨0, by decide⟩
  let slots : List (ScheduledPauli (n + 1)) := (liftSchedule (k := 1) sigma).slots
  let es0 : ErrorState (n + 1) := dataInputState (k := 1) E
  let globalE : Fin (n + 1) -> Pauli := fun q => es0.paulis q
  let esPrep := propagateCircuit (eraseFaults (prep0 anc)) es0
  let esSlots := propagateCircuit (eraseFaults (zParitySlotsCircuit anc slots)) esPrep
  have hprep := prep0_state_for_chain anc es0
  have hne : ∀ slot, slot ∈ slots -> slot.qubit ≠ anc := by
    intro slot hmem
    have hmem' : slot ∈ sigma.slots.map (liftSlot (k := 1)) := by
      simpa [slots, liftSchedule] using hmem
    rcases List.mem_map.mp hmem' with ⟨src, _hsrc, rfl⟩
    simpa [anc, liftSlot] using
      (freshDataQ_ne_freshHelperQ (n := n) (k := 1) src.qubit ⟨0, by decide⟩)
  have hdata : ∀ q : Fin (n + 1), q ≠ anc -> esPrep.paulis q = globalE q := by
    intro q hq
    simpa [globalE, es0, esPrep] using hprep.2.1 q hq
  have hanc : esPrep.paulis anc = xOfBool false := by
    simpa [esPrep] using hprep.1
  have hchain := zParitySlotsCircuit_chain anc slots globalE false esPrep hne hdata hanc
  have hread := zParitySlotsCircuit_preserves_readout anc slots esPrep
  have hcursorPrep : esPrep.detectorCursor = 0 := by
    simpa [esPrep, es0, dataInputState] using hprep.2.2.2
  have hcursorSlots : esSlots.detectorCursor = 0 := by
    calc
      esSlots.detectorCursor = esPrep.detectorCursor := by
        simpa [esSlots] using hread.2
      _ = 0 := hcursorPrep
  have hparity :
      scheduleParityList slots globalE false = scheduleParity sigma E := by
    simpa [slots, globalE, es0] using
      scheduleParityList_liftSchedule (k := 1) sigma E
  have hancSlots :
      esSlots.paulis anc = xOfBool (scheduleParityList slots globalE false) := by
    simpa [esSlots] using hchain.1
  have hfinal :
      (propagateCircuit (eraseFaults (flagMeasZ anc)) esSlots).detectors 0 =
        scheduleParity sigma E := by
    calc
      (propagateCircuit (eraseFaults (flagMeasZ anc)) esSlots).detectors 0
          = hasXComp (esSlots.paulis anc) :=
            flagMeasZ_detector_zero anc esSlots hcursorSlots
      _ = hasXComp (xOfBool (scheduleParityList slots globalE false)) := by
            rw [hancSlots]
      _ = scheduleParityList slots globalE false := by simp
      _ = scheduleParity sigma E := hparity
  have hcompiled :
      propagateCircuit (eraseFaults (prep0 anc ++ zParitySlotsCircuit anc slots ++ flagMeasZ anc)) es0 =
        propagateCircuit (eraseFaults (flagMeasZ anc)) esSlots := by
    simp [zParitySlotsCircuit, esPrep, esSlots, eraseFaults_append,
      QHL.Target.propagateCircuit_append]
  have hfull :
      (propagateCircuit
          (eraseFaults (prep0 anc ++ zParitySlotsCircuit anc slots ++ flagMeasZ anc))
          es0).detectors 0 =
        scheduleParity sigma E := by
    rw [hcompiled]
    exact hfinal
  change
    detectorXor [0]
      (propagateCircuit
        (eraseFaults (prep0 anc ++ zParitySlotsCircuit anc slots ++ flagMeasZ anc))
        es0) =
      scheduleParity sigma E
  simpa [detectorXor] using hfull

theorem compileFreshGadget_Flag_correct {n : Nat} (sigma : RuleSchedule n) :
    GadgetDetectorCorrect .Flag sigma := by
  intro E
  let anc : Fin (n + 2) := freshHelperQ n 2 ⟨0, by decide⟩
  let flg : Fin (n + 2) := freshHelperQ n 2 ⟨1, by decide⟩
  let slots : List (ScheduledPauli (n + 2)) := (liftSchedule (k := 2) sigma).slots
  let half : Nat := slots.length / 2
  let first := slots.take half
  let second := slots.drop half
  let es0 : ErrorState (n + 2) := dataInputState (k := 2) E
  let globalE : Fin (n + 2) -> Pauli := fun q => es0.paulis q
  let esPrepA := propagateCircuit (eraseFaults (prep0 anc)) es0
  let esPrepF := propagateCircuit (eraseFaults (prepP flg)) esPrepA
  let esFirst := propagateCircuit (eraseFaults (zParitySlotsCircuit anc first)) esPrepF
  let esFlag1 := propagateCircuit (eraseFaults (cnot flg anc)) esFirst
  let esSecond := propagateCircuit (eraseFaults (zParitySlotsCircuit anc second)) esFlag1
  let esFlag2 := propagateCircuit (eraseFaults (cnot flg anc)) esSecond
  let esSynd := propagateCircuit (eraseFaults (flagMeasZ anc)) esFlag2
  have hprepA := prep0_state_for_chain anc es0
  have hprepF := prepP_state_for_chain flg esPrepA
  have hanc_ne_flg : anc ≠ flg := by
    intro h
    have hv := congrArg Fin.val h
    simp [anc, flg, freshHelperQ] at hv
  have hflg_ne_anc : flg ≠ anc := fun h => hanc_ne_flg h.symm
  have hslots_ne_anc : ∀ slot, slot ∈ slots -> slot.qubit ≠ anc := by
    intro slot hmem
    have hmem' : slot ∈ sigma.slots.map (liftSlot (k := 2)) := by
      simpa [slots, liftSchedule] using hmem
    rcases List.mem_map.mp hmem' with ⟨src, _hsrc, rfl⟩
    simpa [anc, liftSlot] using
      (freshDataQ_ne_freshHelperQ (n := n) (k := 2) src.qubit ⟨0, by decide⟩)
  have hslots_ne_flg : ∀ slot, slot ∈ slots -> slot.qubit ≠ flg := by
    intro slot hmem
    have hmem' : slot ∈ sigma.slots.map (liftSlot (k := 2)) := by
      simpa [slots, liftSchedule] using hmem
    rcases List.mem_map.mp hmem' with ⟨src, _hsrc, rfl⟩
    simpa [flg, liftSlot] using
      (freshDataQ_ne_freshHelperQ (n := n) (k := 2) src.qubit ⟨1, by decide⟩)
  have hfirst_ne_anc : ∀ slot, slot ∈ first -> slot.qubit ≠ anc := by
    intro slot hmem
    exact hslots_ne_anc slot (by simpa [first] using List.mem_of_mem_take hmem)
  have hsecond_ne_anc : ∀ slot, slot ∈ second -> slot.qubit ≠ anc := by
    intro slot hmem
    exact hslots_ne_anc slot (by simpa [second] using List.mem_of_mem_drop hmem)
  have hdataPrepF : ∀ q : Fin (n + 2), q ≠ anc -> esPrepF.paulis q = globalE q := by
    intro q hqAnc
    by_cases hqFlg : q = flg
    · subst q
      have hclean : esPrepF.paulis flg = xOfBool false := by
        simpa [esPrepF] using hprepF.1
      simpa [globalE, es0, flg] using hclean
    · have hF : esPrepF.paulis q = esPrepA.paulis q := by
        simpa [esPrepF] using hprepF.2.1 q hqFlg
      have hA : esPrepA.paulis q = es0.paulis q := by
        simpa [esPrepA] using hprepA.2.1 q hqAnc
      simpa [globalE] using hF.trans hA
  have hancPrepF : esPrepF.paulis anc = xOfBool false := by
    have hF : esPrepF.paulis anc = esPrepA.paulis anc := by
      simpa [esPrepF] using hprepF.2.1 anc hanc_ne_flg
    have hA : esPrepA.paulis anc = xOfBool false := by
      simpa [esPrepA] using hprepA.1
    exact hF.trans hA
  have hfirst :=
    zParitySlotsCircuit_chain anc first globalE false esPrepF
      hfirst_ne_anc hdataPrepF hancPrepF
  have hreadFirst := zParitySlotsCircuit_preserves_readout anc first esPrepF
  have hflagFirst : esFirst.paulis flg = xOfBool false := by
    have h := hfirst.2 flg hflg_ne_anc
    simpa [esFirst, globalE, es0, flg] using h
  have hancFirst :
      esFirst.paulis anc = xOfBool (scheduleParityList first globalE false) := by
    simpa [esFirst] using hfirst.1
  have hflag1 :=
    cleanFlagCnot_preserves_anc flg anc esFirst
      (scheduleParityList first globalE false) hflg_ne_anc hflagFirst hancFirst
  have hdataFlag1 : ∀ q : Fin (n + 2), q ≠ anc -> esFlag1.paulis q = globalE q := by
    intro q hqAnc
    by_cases hqFlg : q = flg
    · subst q
      have h := hflag1.2.1
      simpa [esFlag1, globalE, es0, flg] using h
    · have hC : esFlag1.paulis q = esFirst.paulis q := by
        simpa [esFlag1] using hflag1.2.2.1 q hqAnc hqFlg
      have hF : esFirst.paulis q = globalE q := hfirst.2 q hqAnc
      exact hC.trans hF
  have hancFlag1 :
      esFlag1.paulis anc = xOfBool (scheduleParityList first globalE false) := by
    simpa [esFlag1] using hflag1.1
  have hsecond :=
    zParitySlotsCircuit_chain anc second globalE
      (scheduleParityList first globalE false) esFlag1
      hsecond_ne_anc hdataFlag1 hancFlag1
  have hreadSecond := zParitySlotsCircuit_preserves_readout anc second esFlag1
  have hflagSecond : esSecond.paulis flg = xOfBool false := by
    have h := hsecond.2 flg hflg_ne_anc
    simpa [esSecond, globalE, es0, flg] using h
  have hancSecond :
      esSecond.paulis anc =
        xOfBool (scheduleParityList second globalE
          (scheduleParityList first globalE false)) := by
    simpa [esSecond] using hsecond.1
  have hflag2 :=
    cleanFlagCnot_preserves_anc flg anc esSecond
      (scheduleParityList second globalE (scheduleParityList first globalE false))
      hflg_ne_anc hflagSecond hancSecond
  have hancFlag2 :
      esFlag2.paulis anc =
        xOfBool (scheduleParityList second globalE
          (scheduleParityList first globalE false)) := by
    simpa [esFlag2] using hflag2.1
  have hcursorPrepF : esPrepF.detectorCursor = 0 := by
    have hpa : esPrepA.detectorCursor = 0 := by
      simpa [esPrepA, es0, dataInputState] using hprepA.2.2.2
    calc
      esPrepF.detectorCursor = esPrepA.detectorCursor := by
        simpa [esPrepF] using hprepF.2.2.2
      _ = 0 := hpa
  have hcursorFirst : esFirst.detectorCursor = 0 := by
    calc
      esFirst.detectorCursor = esPrepF.detectorCursor := by
        simpa [esFirst] using hreadFirst.2
      _ = 0 := hcursorPrepF
  have hcursorFlag1 : esFlag1.detectorCursor = 0 := by
    calc
      esFlag1.detectorCursor = esFirst.detectorCursor := by
        simpa [esFlag1] using hflag1.2.2.2.2
      _ = 0 := hcursorFirst
  have hcursorSecond : esSecond.detectorCursor = 0 := by
    calc
      esSecond.detectorCursor = esFlag1.detectorCursor := by
        simpa [esSecond] using hreadSecond.2
      _ = 0 := hcursorFlag1
  have hcursorFlag2 : esFlag2.detectorCursor = 0 := by
    calc
      esFlag2.detectorCursor = esSecond.detectorCursor := by
        simpa [esFlag2] using hflag2.2.2.2.2
      _ = 0 := hcursorSecond
  have hsplit :
      scheduleParityList second globalE (scheduleParityList first globalE false) =
        scheduleParityList slots globalE false := by
    simpa [first, second] using scheduleParityList_take_drop slots half globalE false
  have hparity :
      scheduleParityList slots globalE false = scheduleParity sigma E := by
    simpa [slots, globalE, es0] using
      scheduleParityList_liftSchedule (k := 2) sigma E
  have hsynd :
      esSynd.detectors 0 = scheduleParity sigma E := by
    calc
      esSynd.detectors 0 = hasXComp (esFlag2.paulis anc) := by
        simpa [esSynd] using flagMeasZ_detector_zero anc esFlag2 hcursorFlag2
      _ = hasXComp
            (xOfBool (scheduleParityList second globalE
              (scheduleParityList first globalE false))) := by
            rw [hancFlag2]
      _ = scheduleParityList second globalE (scheduleParityList first globalE false) := by
            simp
      _ = scheduleParityList slots globalE false := hsplit
      _ = scheduleParity sigma E := hparity
  have hcursorSynd : esSynd.detectorCursor = 1 := by
    simp [esSynd, flagMeasZ, eraseFaults, propagateCircuit, propagateGate, hcursorFlag2]
  have htail :
      (propagateCircuit (eraseFaults (hadamard flg ++ flagMeasZ flg)) esSynd).detectors 0 =
        scheduleParity sigma E := by
    rw [flagTail_preserves_detector_zero flg esSynd hcursorSynd]
    exact hsynd
  have hcompiled :
      propagateCircuit
          (eraseFaults
            (prep0 anc ++ prepP flg ++ zParitySlotsCircuit anc first ++ cnot flg anc ++
              zParitySlotsCircuit anc second ++ cnot flg anc ++ flagMeasZ anc ++
              hadamard flg ++ flagMeasZ flg))
          es0 =
        propagateCircuit (eraseFaults (hadamard flg ++ flagMeasZ flg)) esSynd := by
    simp [zParitySlotsCircuit, esPrepA, esPrepF, esFirst, esFlag1, esSecond,
      esFlag2, esSynd, eraseFaults_append, QHL.Target.propagateCircuit_append]
  have hfull :
      (propagateCircuit
          (eraseFaults
            (prep0 anc ++ prepP flg ++ zParitySlotsCircuit anc first ++ cnot flg anc ++
              zParitySlotsCircuit anc second ++ cnot flg anc ++ flagMeasZ anc ++
              hadamard flg ++ flagMeasZ flg))
          es0).detectors 0 =
        scheduleParity sigma E := by
    rw [hcompiled]
    exact htail
  change
    detectorXor [0]
      (propagateCircuit
        (eraseFaults
          (prep0 anc ++ prepP flg ++ zParitySlotsCircuit anc first ++ cnot flg anc ++
            zParitySlotsCircuit anc second ++ cnot flg anc ++ flagMeasZ anc ++
            hadamard flg ++ flagMeasZ flg))
        es0) =
      scheduleParity sigma E
  simpa [detectorXor] using hfull

theorem compileFreshGadget_Knill_correct {n : Nat} (sigma : RuleSchedule n) :
    GadgetDetectorCorrect .Knill sigma := by
  intro E
  let w : Nat := sigma.slots.length
  let slots : List (ScheduledPauli (n + w)) := (liftSchedule (k := w) sigma).slots
  let ancillas : List (Fin (n + w)) := freshKnillAncillas n w
  let pairs : List (ScheduledPauli (n + w) × Fin (n + w)) := List.zip slots ancillas
  let es0 : ErrorState (n + w) := dataInputState (k := w) E
  let globalE : Fin (n + w) -> Pauli := fun q => es0.paulis q
  have hslot_mem :
      ∀ slot, slot ∈ slots ->
        ∃ src, src ∈ sigma.slots ∧ slot = liftSlot (k := w) src := by
    intro slot hmem
    have hmem' : slot ∈ sigma.slots.map (liftSlot (k := w)) := by
      simpa [slots, liftSchedule] using hmem
    rcases List.mem_map.mp hmem' with ⟨src, hsrc, rfl⟩
    exact ⟨src, hsrc, rfl⟩
  have hanc_mem :
      ∀ anc, anc ∈ ancillas -> ∃ a : Fin w, anc = freshHelperQ n w a := by
    intro anc hmem
    have hmem' : anc ∈ (List.finRange w).map (freshHelperQ n w) := by
      simpa [ancillas, freshKnillAncillas] using hmem
    rcases List.mem_map.mp hmem' with ⟨a, _ha, rfl⟩
    exact ⟨a, rfl⟩
  have hslot_ne_anc :
      ∀ slotPair, slotPair ∈ pairs ->
        ∀ ancPair, ancPair ∈ pairs -> slotPair.1.qubit ≠ ancPair.2 := by
    intro slotPair hslotPair ancPair hancPair
    have hs_mem : slotPair.1 ∈ slots := (List.of_mem_zip hslotPair).1
    have ha_mem : ancPair.2 ∈ ancillas := (List.of_mem_zip hancPair).2
    rcases hslot_mem slotPair.1 hs_mem with ⟨src, _hsrc, hsrcEq⟩
    rcases hanc_mem ancPair.2 ha_mem with ⟨a, haEq⟩
    rw [hsrcEq, haEq]
    simpa [liftSlot] using
      (freshDataQ_ne_freshHelperQ (n := n) (k := w) src.qubit a)
  have hself : ∀ pair, pair ∈ pairs -> pair.1.qubit ≠ pair.2 := by
    intro pair hmem
    exact hslot_ne_anc pair hmem pair hmem
  have hdata : ∀ pair, pair ∈ pairs ->
      es0.paulis pair.1.qubit = globalE pair.1.qubit := by
    intro pair _hmem
    rfl
  have hchain :=
    knillPairsCircuit_chain pairs globalE false es0 0 rfl hdata hself hslot_ne_anc
  have hpairs_len : pairs.length = w := by
    simp [pairs, slots, ancillas, freshKnillAncillas, liftSchedule, w]
  have hslots_le_ancillas : slots.length ≤ ancillas.length := by
    simp [slots, ancillas, freshKnillAncillas, liftSchedule, w]
  have hmapPairs : pairs.map Prod.fst = slots := by
    simpa [pairs] using List.map_fst_zip hslots_le_ancillas
  have hparity :
      scheduleParityList (pairs.map Prod.fst) globalE false = scheduleParity sigma E := by
    rw [hmapPairs]
    simpa [slots, globalE, es0, w] using
      scheduleParityList_liftSchedule (k := w) sigma E
  have hcompiled :
      propagateCircuit (eraseFaults (compileFreshGadget .Knill sigma)) es0 =
        propagateCircuit (eraseFaults (knillPairsCircuit pairs)) es0 := by
    simp [compileFreshGadget, compileGadgetOrdered, compileKnillOrdered,
      freshRuleSchedule, freshAncillaConfig, helperCount, knillPairsCircuit, pairs, slots,
      ancillas, w]
  have hfinal :
      detectorXor (List.range w)
        (propagateCircuit (eraseFaults (knillPairsCircuit pairs)) es0) =
        scheduleParity sigma E := by
    calc
      detectorXor (List.range w)
          (propagateCircuit (eraseFaults (knillPairsCircuit pairs)) es0)
          = detectorXorFromAcc 0 w
              (propagateCircuit (eraseFaults (knillPairsCircuit pairs)) es0) false :=
            detectorXor_range_eq_fromAcc w _
      _ = detectorXorFromAcc 0 pairs.length
              (propagateCircuit (eraseFaults (knillPairsCircuit pairs)) es0) false := by
            rw [hpairs_len]
      _ = scheduleParityList (pairs.map Prod.fst) globalE false := hchain.1
      _ = scheduleParity sigma E := hparity
  change
    detectorXor (List.range w)
      (propagateCircuit (eraseFaults (compileFreshGadget .Knill sigma)) es0) =
      scheduleParity sigma E
  rw [hcompiled]
  exact hfinal

theorem compileFreshGadget_Shor_correct {n : Nat} (sigma0 : RuleSchedule n) :
    GadgetDetectorCorrect .Shor sigma0 := by
  intro E
  cases sigma0 with
  | mk sourceSlots0 =>
    cases sourceSlots0 with
    | nil =>
        simp [compileFreshGadget, compileGadgetOrdered, compileShorOrdered,
          freshAncillaConfig, helperCount, freshShorCat, readoutOffsets,
          gadgetDetectorBit, detectorXor, scheduleParity, dataInputState]
    | cons first rest =>
        let sourceSlots := first :: rest
        let sigma : RuleSchedule n := ⟨sourceSlots⟩
        let w : Nat := sourceSlots.length
        let slots : List (ScheduledPauli (n + (w + 1))) :=
          (liftSchedule (k := w + 1) sigma).slots
        let cat : List (Fin (n + (w + 1))) := freshShorCat n w
        let verifier : Fin (n + (w + 1)) :=
          freshHelperQ n (w + 1) ⟨w, Nat.lt_succ_self w⟩
        let pairs : List (ScheduledPauli (n + (w + 1)) × Fin (n + (w + 1))) :=
          List.zip slots cat
        let es0 : ErrorState (n + (w + 1)) := dataInputState (k := w + 1) E
        let globalE : Fin (n + (w + 1)) -> Pauli := fun q => es0.paulis q
        have hw_pos : 0 < w := by simp [w, sourceSlots]
        have hcat_len : cat.length = w := by simp [cat, freshShorCat]
        cases hcatShape : cat with
        | nil =>
            have : w = 0 := by
              simpa [hcatShape] using hcat_len.symm
            omega
        | cons c0 catRest =>
            let cat' : List (Fin (n + (w + 1))) := c0 :: catRest
            let last : Fin (n + (w + 1)) := cat'.getLast (by simp [cat'])
            let esCat := propagateCircuit (eraseFaults (orderedCatPrepZ cat')) es0
            let esPrepV := propagateCircuit (eraseFaults (prepP verifier)) esCat
            let esCnot1 := propagateCircuit (eraseFaults (cnot verifier c0)) esPrepV
            let esCnot2 := propagateCircuit (eraseFaults (cnot verifier last)) esCnot1
            let esHad := propagateCircuit (eraseFaults (hadamard verifier)) esCnot2
            let esPrefix := propagateCircuit (eraseFaults (flagMeasZ verifier)) esHad
            let esCoupled := propagateCircuit (eraseFaults (shorCouplingPairsCircuit pairs)) esPrefix
            have hcat_eq : cat = cat' := by simp [cat', hcatShape]
            have hcatClean0 :
                ∀ q, q ∈ cat -> es0.paulis q = Pauli.I := by
              intro q hmem
              rcases mem_freshShorCat_helper (n := n) (w := w) hmem with ⟨a, rfl⟩
              simp [es0]
            have hverClean0 : es0.paulis verifier = Pauli.I := by
              simp [es0, verifier]
            have hcatPrep :=
              orderedCatPrepZ_clean_preserves_all cat' es0 (by
                intro q hmem
                exact hcatClean0 q (by simpa [hcat_eq] using hmem))
            have hesCatPaulis : esCat.paulis = es0.paulis := by
              simpa [esCat] using hcatPrep.1
            have hesCatCursor : esCat.detectorCursor = 0 := by
              calc
                esCat.detectorCursor = es0.detectorCursor := by
                  simpa [esCat] using hcatPrep.2.2
                _ = 0 := by simp [es0, dataInputState]
            have hprepV := prepP_state_for_chain verifier esCat
            have hesPrepVPaulis : esPrepV.paulis = es0.paulis := by
              funext q
              by_cases hq : q = verifier
              · subst q
                simpa [esPrepV, hesCatPaulis, hverClean0, xOfBool] using hprepV.1
              · have hpres := hprepV.2.1 q hq
                rw [hpres, hesCatPaulis]
            have hesPrepVCursor : esPrepV.detectorCursor = 0 := by
              calc
                esPrepV.detectorCursor = esCat.detectorCursor := by
                  simpa [esPrepV] using hprepV.2.2.2
                _ = 0 := hesCatCursor
            have hc0CleanPrep : esPrepV.paulis c0 = Pauli.I := by
              rw [hesPrepVPaulis]
              exact hcatClean0 c0 (by simp [hcat_eq, cat'])
            have hverCleanPrep : esPrepV.paulis verifier = Pauli.I := by
              rw [hesPrepVPaulis]
              exact hverClean0
            have hcnot1 :=
              cleanCnot_preserves_all verifier c0 esPrepV hverCleanPrep hc0CleanPrep
            have hesCnot1Paulis : esCnot1.paulis = es0.paulis := by
              calc
                esCnot1.paulis = esPrepV.paulis := by simpa [esCnot1] using hcnot1.1
                _ = es0.paulis := hesPrepVPaulis
            have hesCnot1Cursor : esCnot1.detectorCursor = 0 := by
              calc
                esCnot1.detectorCursor = esPrepV.detectorCursor := by
                  simpa [esCnot1] using hcnot1.2.2
                _ = 0 := hesPrepVCursor
            have hlast_mem_cat : last ∈ cat := by
              have hlast : last ∈ cat' := by
                simp [last, cat']
              simpa [hcat_eq] using hlast
            have hlastClean : esCnot1.paulis last = Pauli.I := by
              rw [hesCnot1Paulis]
              exact hcatClean0 last hlast_mem_cat
            have hverCleanCnot1 : esCnot1.paulis verifier = Pauli.I := by
              rw [hesCnot1Paulis]
              exact hverClean0
            have hcnot2 :=
              cleanCnot_preserves_all verifier last esCnot1 hverCleanCnot1 hlastClean
            have hesCnot2Paulis : esCnot2.paulis = es0.paulis := by
              calc
                esCnot2.paulis = esCnot1.paulis := by simpa [esCnot2] using hcnot2.1
                _ = es0.paulis := hesCnot1Paulis
            have hesCnot2Cursor : esCnot2.detectorCursor = 0 := by
              calc
                esCnot2.detectorCursor = esCnot1.detectorCursor := by
                  simpa [esCnot2] using hcnot2.2.2
                _ = 0 := hesCnot1Cursor
            have hverCleanCnot2 : esCnot2.paulis verifier = Pauli.I := by
              rw [hesCnot2Paulis]
              exact hverClean0
            have hhad := hadamard_clean_preserves_all verifier esCnot2 hverCleanCnot2
            have hesHadPaulis : esHad.paulis = es0.paulis := by
              calc
                esHad.paulis = esCnot2.paulis := by simpa [esHad] using hhad.1
                _ = es0.paulis := hesCnot2Paulis
            have hesHadCursor : esHad.detectorCursor = 0 := by
              calc
                esHad.detectorCursor = esCnot2.detectorCursor := by
                  simpa [esHad] using hhad.2.2
                _ = 0 := hesCnot2Cursor
            have hverCleanHad : esHad.paulis verifier = Pauli.I := by
              rw [hesHadPaulis]
              exact hverClean0
            have hflag := flagMeasZ_clean_cursor verifier esHad 0 hverCleanHad hesHadCursor
            have hesPrefixPaulis : esPrefix.paulis = es0.paulis := by
              calc
                esPrefix.paulis = esHad.paulis := by simpa [esPrefix] using hflag.2.2
                _ = es0.paulis := hesHadPaulis
            have hesPrefixCursor : esPrefix.detectorCursor = 1 := by
              simpa [esPrefix] using hflag.2.1
            have hslot_mem :
                ∀ slot, slot ∈ slots ->
                  ∃ src, src ∈ sourceSlots ∧ slot = liftSlot (k := w + 1) src := by
              intro slot hmem
              have hmem' : slot ∈ sourceSlots.map (liftSlot (k := w + 1)) := by
                simpa [slots, sigma, liftSchedule] using hmem
              rcases List.mem_map.mp hmem' with ⟨src, hsrc, rfl⟩
              exact ⟨src, hsrc, rfl⟩
            have hslot_ne_cat :
                ∀ slotPair, slotPair ∈ pairs ->
                  ∀ catPair, catPair ∈ pairs -> slotPair.1.qubit ≠ catPair.2 := by
              intro slotPair hslotPair catPair hcatPair
              have hs_mem : slotPair.1 ∈ slots := (List.of_mem_zip hslotPair).1
              have hc_mem : catPair.2 ∈ cat := (List.of_mem_zip hcatPair).2
              rcases hslot_mem slotPair.1 hs_mem with ⟨src, _hsrc, hsrcEq⟩
              rcases mem_freshShorCat_helper (n := n) (w := w) hc_mem with ⟨a, haEq⟩
              rw [hsrcEq, haEq]
              simpa [liftSlot] using
                (freshDataQ_ne_freshHelperQ (n := n) (k := w + 1) src.qubit
                  ⟨a.val, by exact Nat.lt_trans a.isLt (Nat.lt_succ_self w)⟩)
            have hcat_nodup : cat.Nodup := by
              simpa [cat] using freshShorCat_nodup n w
            have hpairs_nodup : pairs.Nodup := by
              exact zip_nodup_of_right_nodup slots cat hcat_nodup
            have hcat_ne :
                ∀ pairA, pairA ∈ pairs ->
                  ∀ pairB, pairB ∈ pairs -> pairA ≠ pairB -> pairA.2 ≠ pairB.2 := by
              exact zip_right_ne_of_right_nodup slots cat hcat_nodup
            have hcouple :=
              shorCouplingPairsCircuit_chain pairs globalE esPrefix hpairs_nodup
                (by
                  intro pair hmem
                  simpa [globalE] using congrFun hesPrefixPaulis pair.1.qubit)
                (by
                  intro pair hmem
                  have hc_mem : pair.2 ∈ cat := (List.of_mem_zip hmem).2
                  rw [hesPrefixPaulis]
                  simpa [xOfBool] using hcatClean0 pair.2 hc_mem)
                (by
                  intro pair hmem
                  exact hslot_ne_cat pair hmem pair hmem)
                hslot_ne_cat hcat_ne
            have hcoupledCursor : esCoupled.detectorCursor = 1 := by
              calc
                esCoupled.detectorCursor = esPrefix.detectorCursor := by
                  simpa [esCoupled] using hcouple.2.2.2
                _ = 1 := hesPrefixCursor
            have hraw :=
              rawMeasZPairsCircuit_chain pairs globalE false esCoupled 1
                hcoupledCursor (by
                  intro pair hmem
                  simpa [esCoupled] using hcouple.1 pair hmem)
            have hslots_le_cat : slots.length ≤ cat.length := by
              simp [slots, cat, sigma, liftSchedule, freshShorCat, w, sourceSlots]
            have hcat_le_slots : cat.length ≤ slots.length := by
              simp [slots, cat, sigma, liftSchedule, freshShorCat, w, sourceSlots]
            have hmapPairs : pairs.map Prod.fst = slots := by
              simpa [pairs] using List.map_fst_zip hslots_le_cat
            have hrawPairs : rawMeasZPairsCircuit pairs = (cat.map rawMeasZ).flatten := by
              have hsnd : pairs.map Prod.snd = cat := by
                simpa [pairs] using List.map_snd_zip hcat_le_slots
              unfold rawMeasZPairsCircuit
              rw [← hsnd]
              simp [List.map_map, Function.comp_def]
            have hrawPairsCat : rawMeasZPairsCircuit pairs = (cat'.map rawMeasZ).flatten := by
              rw [hrawPairs, hcat_eq]
            have hpairs_len : pairs.length = w := by
              simp [pairs, slots, cat, sigma, liftSchedule, freshShorCat, w, sourceSlots]
            have hparity :
                scheduleParityList (pairs.map Prod.fst) globalE false =
                  scheduleParity sigma E := by
              rw [hmapPairs]
              simpa [slots, globalE, es0, sigma, w] using
                scheduleParityList_liftSchedule (k := w + 1) sigma E
            have hcatShapeFresh : freshShorCat n (rest.length + 1) = c0 :: catRest := by
              simpa [cat, w, sourceSlots] using hcatShape
            have hcompiledCircuit :
                eraseFaults (compileFreshGadget .Shor sigma) =
                  eraseFaults (orderedCatPrepZ cat') ++
                    eraseFaults (prepP verifier) ++
                    eraseFaults (cnot verifier c0) ++
                    eraseFaults (cnot verifier last) ++
                    eraseFaults (hadamard verifier) ++
                    eraseFaults (flagMeasZ verifier) ++
                    eraseFaults (shorCouplingPairsCircuit pairs) ++
                    eraseFaults ((cat'.map rawMeasZ).flatten) := by
              simp only [compileFreshGadget, compileGadgetOrdered, compileShorOrdered,
                freshRuleSchedule, freshAncillaConfig, helperCount, sigma, sourceSlots, w,
                cat, hcatShape, cat', last, verifier, pairs, slots, shorCouplingPairsCircuit]
              exact eraseFaults_append8 (orderedCatPrepZ (c0 :: catRest))
                (prepP (freshHelperQ n ((first :: rest).length + 1)
                  ⟨(first :: rest).length, Nat.lt_succ_self _⟩))
                (cnot (freshHelperQ n ((first :: rest).length + 1)
                  ⟨(first :: rest).length, Nat.lt_succ_self _⟩) c0)
                (cnot (freshHelperQ n ((first :: rest).length + 1)
                  ⟨(first :: rest).length, Nat.lt_succ_self _⟩)
                  ((c0 :: catRest).getLast (by simp)))
                (hadamard (freshHelperQ n ((first :: rest).length + 1)
                  ⟨(first :: rest).length, Nat.lt_succ_self _⟩))
                (flagMeasZ (freshHelperQ n ((first :: rest).length + 1)
                  ⟨(first :: rest).length, Nat.lt_succ_self _⟩))
                ((List.map (fun pair => shorCouplingSlot pair.1 pair.2)
                  ((liftSchedule { slots := first :: rest }).slots.zip (c0 :: catRest))).flatten)
                ((List.map rawMeasZ (c0 :: catRest)).flatten)
            have hcompiled :
                propagateCircuit (eraseFaults (compileFreshGadget .Shor sigma)) es0 =
                  propagateCircuit (eraseFaults (rawMeasZPairsCircuit pairs)) esCoupled := by
              rw [hrawPairsCat, hcompiledCircuit]
              simpa [esCat, esPrepV, esCnot1, esCnot2, esHad, esPrefix, esCoupled] using
                (propagateCircuit_append8 (eraseFaults (orderedCatPrepZ cat'))
                  (eraseFaults (prepP verifier)) (eraseFaults (cnot verifier c0))
                  (eraseFaults (cnot verifier last)) (eraseFaults (hadamard verifier))
                  (eraseFaults (flagMeasZ verifier))
                  (eraseFaults (shorCouplingPairsCircuit pairs))
                  (eraseFaults ((cat'.map rawMeasZ).flatten)) es0)
            have hfinal :
                detectorXor ((List.range w).map Nat.succ)
                    (propagateCircuit (eraseFaults (rawMeasZPairsCircuit pairs)) esCoupled) =
                  scheduleParity sigma E := by
              calc
                detectorXor ((List.range w).map Nat.succ)
                    (propagateCircuit (eraseFaults (rawMeasZPairsCircuit pairs)) esCoupled)
                    = detectorXorFromAcc 1 w
                        (propagateCircuit (eraseFaults (rawMeasZPairsCircuit pairs)) esCoupled)
                        false :=
                      detectorXor_map_succ_range_eq_fromAcc w _
                _ = detectorXorFromAcc 1 pairs.length
                        (propagateCircuit (eraseFaults (rawMeasZPairsCircuit pairs)) esCoupled)
                        false := by rw [hpairs_len]
                _ = scheduleParityList (pairs.map Prod.fst) globalE false := hraw.1
                _ = scheduleParity sigma E := hparity
            change
              detectorXor ((List.range w).map Nat.succ)
                (propagateCircuit (eraseFaults (compileFreshGadget .Shor sigma)) es0) =
                scheduleParity sigma E
            rw [hcompiled]
            exact hfinal

def gadgetDetectorPre {n : Nat} (scheme : Scheme) (sigma : RuleSchedule n) :
    QHL.Target.AssertionC (n + helperCount scheme sigma) :=
  fun es => ∃ E : Fin n -> Pauli, es = dataInputState (k := helperCount scheme sigma) E

def gadgetDetectorPost {n : Nat} (scheme : Scheme) (sigma : RuleSchedule n) :
    QHL.Target.AssertionC (n + helperCount scheme sigma) :=
  fun es =>
    ∀ E : Fin n -> Pauli,
      es =
          propagateCircuit (eraseFaults (compileFreshGadget scheme sigma))
            (dataInputState (k := helperCount scheme sigma) E) ->
        gadgetDetectorBit scheme sigma es = scheduleParity sigma E

def circuitWPDeriv {nq : Nat} :
    (c : Circuit nq) -> (Post : QHL.Target.AssertionC nq) ->
      QHL.Target.DerivC nq
        (fun es => Post (propagateCircuit c es)) c Post
  | [], Post => QHL.Target.DerivC.C_Nil Post
  | g :: rest, Post =>
      QHL.Target.DerivC.C_App
        (QHL.Target.DerivC.C_Gate g (fun es => Post (propagateCircuit rest es)))
        (circuitWPDeriv rest Post)

def gadgetDetectorWPDeriv {n : Nat} (scheme : Scheme) (sigma : RuleSchedule n) :
    QHL.Target.DerivC (n + helperCount scheme sigma)
      (fun es =>
        gadgetDetectorPost scheme sigma
          (propagateCircuit (eraseFaults (compileFreshGadget scheme sigma)) es))
      (eraseFaults (compileFreshGadget scheme sigma))
      (gadgetDetectorPost scheme sigma) :=
  circuitWPDeriv (eraseFaults (compileFreshGadget scheme sigma))
    (gadgetDetectorPost scheme sigma)

/-- The nontrivial proof obligation for a scheme: show that every data-input
state satisfies the weakest precondition generated by `gadgetDetectorWPDeriv`.
Once this field is filled, `deriv` is a standard QClifford Hoare derivation of
the detector-parity theorem for that scheme and schedule. -/
structure GadgetDetectorHoareCertificate {n : Nat}
    (scheme : Scheme) (sigma : RuleSchedule n) where
  pre_implies_wp :
    ∀ es,
      gadgetDetectorPre scheme sigma es ->
        gadgetDetectorPost scheme sigma
          (propagateCircuit (eraseFaults (compileFreshGadget scheme sigma)) es)
  deriv :
    QHL.Target.DerivC (n + helperCount scheme sigma)
      (gadgetDetectorPre scheme sigma)
      (eraseFaults (compileFreshGadget scheme sigma))
      (gadgetDetectorPost scheme sigma) :=
    QHL.Target.DerivC.C_Consequence
      (gadgetDetectorWPDeriv scheme sigma)
      pre_implies_wp
      (fun _ h => h)

def gadgetDetectorHoareCertificateOfCorrect {n : Nat}
    {scheme : Scheme} {sigma : RuleSchedule n}
    (hcorrect : GadgetDetectorCorrect scheme sigma) :
    GadgetDetectorHoareCertificate scheme sigma where
  pre_implies_wp := by
    intro es hpre
    rcases hpre with ⟨E0, rfl⟩
    intro E hEq
    rw [hEq]
    exact hcorrect E

def compileFreshGadget_NZ_hoareCertificate {n : Nat} (sigma : RuleSchedule n) :
    GadgetDetectorHoareCertificate .NZ sigma :=
  gadgetDetectorHoareCertificateOfCorrect (compileFreshGadget_NZ_correct sigma)

def compileFreshGadget_Flag_hoareCertificate {n : Nat} (sigma : RuleSchedule n) :
    GadgetDetectorHoareCertificate .Flag sigma :=
  gadgetDetectorHoareCertificateOfCorrect (compileFreshGadget_Flag_correct sigma)

def compileFreshGadget_Knill_hoareCertificate {n : Nat} (sigma : RuleSchedule n) :
    GadgetDetectorHoareCertificate .Knill sigma :=
  gadgetDetectorHoareCertificateOfCorrect (compileFreshGadget_Knill_correct sigma)

def compileFreshGadget_Shor_hoareCertificate {n : Nat} (sigma : RuleSchedule n) :
    GadgetDetectorHoareCertificate .Shor sigma :=
  gadgetDetectorHoareCertificateOfCorrect (compileFreshGadget_Shor_correct sigma)

def compileFreshGadget_NZ_deriv {n : Nat} (sigma : RuleSchedule n) :
    QHL.Target.DerivC (n + helperCount .NZ sigma)
      (gadgetDetectorPre .NZ sigma)
      (eraseFaults (compileFreshGadget .NZ sigma))
      (gadgetDetectorPost .NZ sigma) :=
  (compileFreshGadget_NZ_hoareCertificate sigma).deriv

def compileFreshGadget_Flag_deriv {n : Nat} (sigma : RuleSchedule n) :
    QHL.Target.DerivC (n + helperCount .Flag sigma)
      (gadgetDetectorPre .Flag sigma)
      (eraseFaults (compileFreshGadget .Flag sigma))
      (gadgetDetectorPost .Flag sigma) :=
  (compileFreshGadget_Flag_hoareCertificate sigma).deriv

def compileFreshGadget_Knill_deriv {n : Nat} (sigma : RuleSchedule n) :
    QHL.Target.DerivC (n + helperCount .Knill sigma)
      (gadgetDetectorPre .Knill sigma)
      (eraseFaults (compileFreshGadget .Knill sigma))
      (gadgetDetectorPost .Knill sigma) :=
  (compileFreshGadget_Knill_hoareCertificate sigma).deriv

def compileFreshGadget_Shor_deriv {n : Nat} (sigma : RuleSchedule n) :
    QHL.Target.DerivC (n + helperCount .Shor sigma)
      (gadgetDetectorPre .Shor sigma)
      (eraseFaults (compileFreshGadget .Shor sigma))
      (gadgetDetectorPost .Shor sigma) :=
  (compileFreshGadget_Shor_hoareCertificate sigma).deriv

def programWPDeriv {n : Nat} (program : XZProgram n)
    (Post : QHL.Target.AssertionC (n + programHelperCount program)) :
    QHL.Target.DerivC (n + programHelperCount program)
      (fun es => Post (propagateCircuit (eraseFaults (compileProgram program)) es))
      (eraseFaults (compileProgram program))
      Post :=
  circuitWPDeriv (eraseFaults (compileProgram program)) Post

namespace FreshExamples

def q0 : Fin 4 := ⟨0, by decide⟩
def q1 : Fin 4 := ⟨1, by decide⟩
def q2 : Fin 4 := ⟨2, by decide⟩
def q3 : Fin 4 := ⟨3, by decide⟩

def XXZZ : RuleSchedule 4 :=
  ⟨[⟨.X, q0⟩, ⟨.X, q1⟩, ⟨.Z, q2⟩, ⟨.Z, q3⟩]⟩

def ZZXX : RuleSchedule 4 :=
  ⟨[⟨.Z, q0⟩, ⟨.Z, q1⟩, ⟨.X, q2⟩, ⟨.X, q3⟩]⟩

def ZXZX : RuleSchedule 4 :=
  ⟨[⟨.Z, q0⟩, ⟨.X, q1⟩, ⟨.Z, q2⟩, ⟨.X, q3⟩]⟩

def Z0 : RuleSchedule 4 :=
  ⟨[⟨.Z, q0⟩]⟩

def twoFreshNZ : XZProgram 4 :=
  .seq (.meas .NZ Z0) (.meas .NZ Z0)

example : helperCount .NZ XXZZ = 1 := rfl
example : helperCount .Knill XXZZ = 4 := rfl
example : helperCount .Shor XXZZ = 5 := rfl
example : helperCount .Flag XXZZ = 2 := rfl
example : programHelperCount twoFreshNZ = 2 := rfl

example :
    traceCircuit (compileProgram twoFreshNZ) =
      [.errLoc 4, .prepZero 4,
       .errLoc 0, .errLoc 4, .cnot 0 4,
       .errLoc 4, .measZ 4,
       .errLoc 5, .prepZero 5,
       .errLoc 0, .errLoc 5, .cnot 0 5,
       .errLoc 5, .measZ 5] := by
  decide

example :
    traceCircuit (compileFreshGadget .NZ XXZZ) ≠
      traceCircuit (compileFreshGadget .NZ ZZXX) := by
  decide

example :
    traceCircuit (compileFreshGadget .Knill XXZZ) ≠
      traceCircuit (compileFreshGadget .Knill ZZXX) := by
  decide

example :
    traceCircuit (compileFreshGadget .Shor XXZZ) ≠
      traceCircuit (compileFreshGadget .Shor ZZXX) := by
  decide

example :
    traceCircuit (compileFreshGadget .Flag XXZZ) ≠
      traceCircuit (compileFreshGadget .Flag ZZXX) := by
  decide

example :
    traceCircuit (compileFreshGadget .NZ XXZZ) ≠
      traceCircuit (compileFreshGadget .NZ ZXZX) := by
  decide

example :
    traceCircuit (compileFreshGadget .Knill XXZZ) ≠
      traceCircuit (compileFreshGadget .Knill ZXZX) := by
  decide

example :
    traceCircuit (compileFreshGadget .Shor XXZZ) ≠
      traceCircuit (compileFreshGadget .Shor ZXZX) := by
  decide

example :
    traceCircuit (compileFreshGadget .Flag XXZZ) ≠
      traceCircuit (compileFreshGadget .Flag ZXZX) := by
  decide

end FreshExamples

def compileNZ {nq : Nat} (kind : Pauli) (sigma : Schedule nq) (anc : Fin nq) :
    FCircuit nq :=
  match kind with
  | .X =>
      prepP anc ++
      (sigma.support.map (fun q => cnot anc q)).flatten ++
      hadamard anc ++
      flagMeasZ anc
  | .Z =>
      prep0 anc ++
      (sigma.support.map (fun q => cnot q anc)).flatten ++
      flagMeasZ anc
  | _ => []

def compileKnill {nq : Nat} (kind : Pauli) (sigma : Schedule nq)
    (ancillas : List (Fin nq)) : FCircuit nq :=
  match kind with
  | .Z =>
      ((List.zip sigma.support ancillas).map (fun qa =>
        prep0 qa.2 ++ cnot qa.1 qa.2 ++ rawMeasZ qa.2)).flatten
  | .X =>
      ((List.zip sigma.support ancillas).map (fun qa =>
        prepP qa.2 ++ cnot qa.2 qa.1 ++ hadamard qa.2 ++ rawMeasZ qa.2)).flatten
  | _ => []

def catPrep {nq : Nat} (cat : List (Fin nq)) : FCircuit nq :=
  match cat with
  | [] => []
  | c0 :: rest =>
      prepP c0 ++
      ((List.zip (c0 :: rest) rest).map (fun cc => cnot cc.1 cc.2)).flatten

def catPrepZ {nq : Nat} (cat : List (Fin nq)) : FCircuit nq :=
  match cat with
  | [] => []
  | c0 :: rest =>
      prep0 c0 ++
      ((List.zip (c0 :: rest) rest).map (fun cc => cnot cc.1 cc.2)).flatten

def compileShor {nq : Nat} (kind : Pauli) (sigma : Schedule nq)
    (cat : List (Fin nq)) (verifier : Fin nq) : FCircuit nq :=
  match kind, cat with
  | .X, c0 :: rest =>
      let cat' := c0 :: rest
      let last := cat'.getLast (by simp)
      catPrep cat' ++
      prep0 verifier ++
      cnot c0 verifier ++
      cnot last verifier ++
      flagMeasZ verifier ++
      ((List.zip cat' sigma.support).map (fun cq => cnot cq.1 cq.2)).flatten ++
      (cat'.map (fun c => hadamard c ++ rawMeasZ c)).flatten
  | .Z, c0 :: rest =>
      let cat' := c0 :: rest
      let last := cat'.getLast (by simp)
      catPrepZ cat' ++
      prepP verifier ++
      cnot verifier c0 ++
      cnot verifier last ++
      hadamard verifier ++
      flagMeasZ verifier ++
      ((List.zip sigma.support cat').map (fun qc => cnot qc.1 qc.2)).flatten ++
      (cat'.map rawMeasZ).flatten
  | _, _ => []

def compileFlag {nq : Nat} (kind : Pauli) (sigma : Schedule nq)
    (anc flag : Fin nq) : FCircuit nq :=
  match kind with
  | .X =>
      let half := sigma.support.length / 2
      prepP anc ++
      prep0 flag ++
      ((sigma.support.take half).map (fun q => cnot anc q)).flatten ++
      cnot anc flag ++
      ((sigma.support.drop half).map (fun q => cnot anc q)).flatten ++
      cnot anc flag ++
      hadamard anc ++
      flagMeasZ anc ++
      flagMeasZ flag
  | _ => []

def compileGadget {nq : Nat} (scheme : Scheme) (kind : Pauli)
    (sigma : Schedule nq) (anc : AncillaConfig nq) : FCircuit nq :=
  match scheme, anc with
  | .NZ, .nz a => compileNZ kind sigma a
  | .Knill, .knill as => compileKnill kind sigma as
  | .Shor, .shor cat verifier => compileShor kind sigma cat verifier
  | .Flag, .flag a f => compileFlag kind sigma a f
  | _, _ => []

namespace Standard

def schedule {n : Nat} (support : List (Fin n)) : Schedule (n + 1) :=
  ⟨support.map (QStab.QClifford.Standard.mkDataQubit n)⟩

def ancilla (n : Nat) : AncillaConfig (n + 1) :=
  .nz (QStab.QClifford.Standard.ancQubit n)

private theorem erase_cnot_chain_x (n : Nat) (support : List (Fin n)) :
    eraseFaults
        ((support.map (fun q =>
          cnot (QStab.QClifford.Standard.ancQubit n)
            (QStab.QClifford.Standard.mkDataQubit n q))).flatten) =
      support.map (fun q =>
        Gate.cnot (QStab.QClifford.Standard.ancQubit n)
          (QStab.QClifford.Standard.mkDataQubit n q)
          (QStab.QClifford.Standard.anc_ne_data n q)) := by
  induction support with
  | nil => rfl
  | cons q qs ih =>
      simp [eraseFaults_append, ih]
      rw [eraseFaults_cnot (QStab.QClifford.Standard.ancQubit n)
        (QStab.QClifford.Standard.mkDataQubit n q)
        (QStab.QClifford.Standard.anc_ne_data n q)]
      rfl

private theorem erase_cnot_chain_z (n : Nat) (support : List (Fin n)) :
    eraseFaults
        ((support.map (fun q =>
          cnot (QStab.QClifford.Standard.mkDataQubit n q)
            (QStab.QClifford.Standard.ancQubit n))).flatten) =
      support.map (fun q =>
        Gate.cnot (QStab.QClifford.Standard.mkDataQubit n q)
          (QStab.QClifford.Standard.ancQubit n)
          (QStab.QClifford.Standard.data_ne_anc n q)) := by
  induction support with
  | nil => rfl
  | cons q qs ih =>
      simp [eraseFaults_append, ih]
      rw [eraseFaults_cnot (QStab.QClifford.Standard.mkDataQubit n q)
        (QStab.QClifford.Standard.ancQubit n)
        (QStab.QClifford.Standard.data_ne_anc n q)]
      rfl

theorem erase_compileNZ_x_eq_xCircuit (n : Nat) (support : List (Fin n)) :
    eraseFaults (compileGadget .NZ .X (schedule support) (ancilla n)) =
      QStab.QClifford.Standard.xCircuit n support := by
  simp [compileGadget, compileNZ, schedule, ancilla, prepP, hadamard, flagMeasZ,
    QStab.QClifford.Standard.xCircuit]
  simpa [Function.comp_def] using erase_cnot_chain_x n support

theorem erase_compileNZ_z_eq_zCircuit (n : Nat) (support : List (Fin n)) :
    eraseFaults (compileGadget .NZ .Z (schedule support) (ancilla n)) =
      QStab.QClifford.Standard.zCircuit n support := by
  simp [compileGadget, compileNZ, schedule, ancilla, prep0, flagMeasZ,
    QStab.QClifford.Standard.zCircuit]
  simpa [Function.comp_def] using erase_cnot_chain_z n support

end Standard

namespace Knill

def dataQ (n : Nat) (i : Fin n) : Fin (n + n) :=
  ⟨i.val, by have := i.isLt; omega⟩

def ancQ (n : Nat) (i : Fin n) : Fin (n + n) :=
  ⟨n + i.val, by have := i.isLt; omega⟩

def schedule (n : Nat) : Schedule (n + n) :=
  ⟨(List.finRange n).map (dataQ n)⟩

def ancillas (n : Nat) : List (Fin (n + n)) :=
  (List.finRange n).map (ancQ n)

def config (n : Nat) : AncillaConfig (n + n) :=
  .knill (ancillas n)

theorem data_ne_anc (n : Nat) (i : Fin n) : dataQ n i ≠ ancQ n i := by
  intro h
  have hv := congrArg Fin.val h
  simp [dataQ, ancQ] at hv
  omega

@[simp] theorem erase_compileKnill_z_pair (n : Nat) (i : Fin n) :
    eraseFaults (prep0 (ancQ n i) ++ cnot (dataQ n i) (ancQ n i) ++ rawMeasZ (ancQ n i)) =
      [Gate.prepZero (ancQ n i), Gate.cnot (dataQ n i) (ancQ n i) (data_ne_anc n i),
        Gate.measZ (ancQ n i)] := by
  simp [prep0, rawMeasZ, eraseFaults_cnot, data_ne_anc]

theorem erase_compileKnill_z_pairs (n : Nat) (is : List (Fin n)) :
    eraseFaults
        (((is.map (dataQ n)).zip (is.map (ancQ n))).map (fun qa =>
          prep0 qa.2 ++ cnot qa.1 qa.2 ++ rawMeasZ qa.2)).flatten =
      (is.map (fun i =>
        [Gate.prepZero (ancQ n i), Gate.cnot (dataQ n i) (ancQ n i) (data_ne_anc n i),
          Gate.measZ (ancQ n i)])).flatten := by
  induction is with
  | nil => rfl
  | cons i rest ih =>
      change
        eraseFaults
            ((prep0 (ancQ n i) ++ cnot (dataQ n i) (ancQ n i) ++ rawMeasZ (ancQ n i)) ++
              (((rest.map (dataQ n)).zip (rest.map (ancQ n))).map (fun qa =>
                prep0 qa.2 ++ cnot qa.1 qa.2 ++ rawMeasZ qa.2)).flatten) =
          [Gate.prepZero (ancQ n i), Gate.cnot (dataQ n i) (ancQ n i) (data_ne_anc n i),
              Gate.measZ (ancQ n i)] ++
            (rest.map (fun i =>
              [Gate.prepZero (ancQ n i), Gate.cnot (dataQ n i) (ancQ n i) (data_ne_anc n i),
                Gate.measZ (ancQ n i)])).flatten
      rw [eraseFaults_append, erase_compileKnill_z_pair, ih]

theorem erase_compileKnill_z_eq_knillCircuit (n : Nat) :
    eraseFaults (compileGadget .Knill .Z (schedule n) (config n)) =
      QStab.QClifford.Knill.knillCircuit n := by
  simp [compileGadget, compileKnill, schedule, config, ancillas,
    QStab.QClifford.Knill.knillCircuit]
  simpa [QStab.QClifford.Knill.qubitGadget, dataQ, ancQ] using
    erase_compileKnill_z_pairs n (List.finRange n)

end Knill

namespace SurfaceD3

abbrev DataQ := QStab.QClifford.SurfaceD3Distance.DataQ

def physSchedule (order : List DataQ) : Schedule 10 :=
  ⟨order.map QStab.QClifford.SurfaceD3Distance.physOfData⟩

def nzAnc : AncillaConfig 10 :=
  .nz QStab.QClifford.SurfaceD3Distance.anc

@[simp] theorem physOfData_ne_qq9 (q : DataQ) (h : 9 < 10) :
    QStab.QClifford.SurfaceD3Distance.physOfData q ≠
      QStab.QClifford.SurfaceD3Distance.qq 9 h := by
  intro heq
  have hv := congrArg Fin.val heq
  simp [QStab.QClifford.SurfaceD3Distance.physOfData,
    QStab.QClifford.SurfaceD3Distance.qq] at hv
  omega

@[simp] theorem qq9_ne_physOfData (q : DataQ) (h : 9 < 10) :
    QStab.QClifford.SurfaceD3Distance.qq 9 h ≠
      QStab.QClifford.SurfaceD3Distance.physOfData q := by
  exact (physOfData_ne_qq9 q h).symm

theorem compileNZ_z_eq_zGadget (order : List DataQ) :
    compileGadget .NZ .Z (physSchedule order) nzAnc =
      QStab.QClifford.SurfaceD3Distance.zGadget order := by
  induction order with
  | nil =>
      simp [compileGadget, compileNZ, physSchedule, nzAnc,
        QStab.QClifford.SurfaceD3Distance.zGadget,
        QStab.QClifford.SurfaceD3Distance.anc,
        QStab.QClifford.SurfaceD3Distance.qq,
        prep0, flagMeasZ]
  | cons q qs _ =>
      simp [compileGadget, compileNZ, physSchedule, nzAnc,
        QStab.QClifford.SurfaceD3Distance.zGadget,
        QStab.QClifford.SurfaceD3Distance.anc,
        prep0, flagMeasZ, cnot, Function.comp_def]

theorem compileNZ_x_eq_xGadget (order : List DataQ) :
    compileGadget .NZ .X (physSchedule order) nzAnc =
      QStab.QClifford.SurfaceD3Distance.xGadget order := by
  induction order with
  | nil =>
      simp [compileGadget, compileNZ, physSchedule, nzAnc,
        QStab.QClifford.SurfaceD3Distance.xGadget,
        QStab.QClifford.SurfaceD3Distance.anc,
        QStab.QClifford.SurfaceD3Distance.qq,
        prepP, hadamard, flagMeasZ]
  | cons q qs _ =>
      simp [compileGadget, compileNZ, physSchedule, nzAnc,
        QStab.QClifford.SurfaceD3Distance.xGadget,
        QStab.QClifford.SurfaceD3Distance.anc,
        prepP, hadamard, flagMeasZ, cnot, Function.comp_def]

def compiledG0 : FCircuit 10 :=
  compileGadget .NZ .Z
    (physSchedule QStab.QClifford.SurfaceD3Distance.G0Order) nzAnc

def compiledG1 : FCircuit 10 :=
  compileGadget .NZ .X
    (physSchedule QStab.QClifford.SurfaceD3Distance.G1Order) nzAnc

def compiledG2 : FCircuit 10 :=
  compileGadget .NZ .X
    (physSchedule QStab.QClifford.SurfaceD3Distance.G2Order) nzAnc

def compiledG3 : FCircuit 10 :=
  compileGadget .NZ .Z
    (physSchedule QStab.QClifford.SurfaceD3Distance.G3Order) nzAnc

def compiledG4 : FCircuit 10 :=
  compileGadget .NZ .X
    (physSchedule QStab.QClifford.SurfaceD3Distance.G4Order) nzAnc

def compiledG5 : FCircuit 10 :=
  compileGadget .NZ .Z
    (physSchedule QStab.QClifford.SurfaceD3Distance.G5Order) nzAnc

def compiledG6 : FCircuit 10 :=
  compileGadget .NZ .Z
    (physSchedule QStab.QClifford.SurfaceD3Distance.G6Order) nzAnc

def compiledG7 : FCircuit 10 :=
  compileGadget .NZ .X
    (physSchedule QStab.QClifford.SurfaceD3Distance.G7Order) nzAnc

@[simp] theorem compiledG0_eq :
    compiledG0 = QStab.QClifford.SurfaceD3Distance.G0 := by
  simp [compiledG0, QStab.QClifford.SurfaceD3Distance.G0, compileNZ_z_eq_zGadget]

@[simp] theorem compiledG1_eq :
    compiledG1 = QStab.QClifford.SurfaceD3Distance.G1 := by
  simp [compiledG1, QStab.QClifford.SurfaceD3Distance.G1, compileNZ_x_eq_xGadget]

@[simp] theorem compiledG2_eq :
    compiledG2 = QStab.QClifford.SurfaceD3Distance.G2 := by
  simp [compiledG2, QStab.QClifford.SurfaceD3Distance.G2, compileNZ_x_eq_xGadget]

@[simp] theorem compiledG3_eq :
    compiledG3 = QStab.QClifford.SurfaceD3Distance.G3 := by
  simp [compiledG3, QStab.QClifford.SurfaceD3Distance.G3, compileNZ_z_eq_zGadget]

@[simp] theorem compiledG4_eq :
    compiledG4 = QStab.QClifford.SurfaceD3Distance.G4 := by
  simp [compiledG4, QStab.QClifford.SurfaceD3Distance.G4, compileNZ_x_eq_xGadget]

@[simp] theorem compiledG5_eq :
    compiledG5 = QStab.QClifford.SurfaceD3Distance.G5 := by
  simp [compiledG5, QStab.QClifford.SurfaceD3Distance.G5, compileNZ_z_eq_zGadget]

@[simp] theorem compiledG6_eq :
    compiledG6 = QStab.QClifford.SurfaceD3Distance.G6 := by
  simp [compiledG6, QStab.QClifford.SurfaceD3Distance.G6, compileNZ_z_eq_zGadget]

@[simp] theorem compiledG7_eq :
    compiledG7 = QStab.QClifford.SurfaceD3Distance.G7 := by
  simp [compiledG7, QStab.QClifford.SurfaceD3Distance.G7, compileNZ_x_eq_xGadget]

def compiledCircuit : FCircuit 10 :=
  compiledG0 ++ (compiledG1 ++ (compiledG2 ++ (compiledG3 ++
    (compiledG4 ++ (compiledG5 ++ (compiledG6 ++ compiledG7))))))

theorem compiledCircuit_eq_C_NZ_D3 :
    compiledCircuit = QStab.QClifford.SurfaceD3Distance.C_NZ_D3 := by
  simp [compiledCircuit, QStab.QClifford.SurfaceD3Distance.C_NZ_D3]

end SurfaceD3

#print axioms SurfaceD3.compiledCircuit_eq_C_NZ_D3
#print axioms Standard.erase_compileNZ_x_eq_xCircuit
#print axioms Standard.erase_compileNZ_z_eq_zCircuit
#print axioms Knill.erase_compileKnill_z_eq_knillCircuit

end QStab.QClifford.Compile
