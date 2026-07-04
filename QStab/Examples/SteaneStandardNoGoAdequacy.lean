import QStab.Examples.SteaneStandardNoGo
import QStab.QClifford.Compile.NZReachCalculus

/-!
# Discharging `StandardAdequacy steaneSpec` — the CSS pure-Z campaign

Steane is CSS, and this dissolves the completing-fault wall that blocks the five-qubit
(non-CSS) adequacy.  Order the program X-gadgets-first / Z-gadgets-last and run a **pure-Z**
attack.  Then every detector is structurally quiet:

* the three X-gadgets (indices `0,1,2`) run first on *clean* data — the Z-faults are injected only
  later — so their Z-basis detectors read `0`;
* a `Z` error on a data qubit commutes with a Z-gadget's `CX(data, anc)` (`Z` on the control stays
  on the control), so it never flips a Z-detector; and it commutes with a Z-gadget's `measZ`.

This file develops the `runFScript`-level pieces of that campaign.

## What is landed here (all axiom-clean, `decide`-checked or structural)

* `steane_nogo_core_spec` — the spec-level no-go core: every weight-2 suffix hook of the *last*
  Z-stabilizer `Z{3,4,5,6}`, completed by one single-qubit `Z`-fault, embeds on the 13 compiled
  qubits to a genuine `logicalFailure`-shaped fact (`Centralizer steaneSpec ∧ ¬ Stab steaneSpec`).
* `steaneStandardCircuit_decompose` — the honest decomposition of the compiled circuit into its six
  NZ gadget blocks (the target of the `runFScript_append` composition law).
* `runFScript_allNone` — the clean-propagation primitive: an all-`none` script reduces a
  `runFScript` run to plain `propagateCircuit`.
* `runFScript_nzBlock_noInject` — one gadget block on a commuting datum, run with no injection,
  preserves data (off the ancilla), keeps detectors quiet, cleans the ancilla, adds `0` faults.
* `logicalFailure_of_core_spec` — the bridge from the embedded completed hook to `logicalFailure`.

## The remaining obstacle for a *fully parametric* `StandardAdequacy steaneSpec`

The surviving development is a `runFScript`-level **ancilla-hook** block lemma (injecting `Z` on the
last gadget's ancilla mid-ladder, depositing the weight-2 `Z`-suffix hook on its last two data
controls while keeping that gadget's own detector quiet), composed with the completing data-`Z`
fault injected at its coupling in whichever Z-gadget couples it.  This is documented precisely at
the end of the file.  It is neither a `decide` (the injection position is symbolic in `order`) nor
an enumeration (there are `≈ (4! · 3! · 4!)^…` valid circuits).  It is deliberately left
un-assumed (no `sorry`, no axiom, no weakened theorem).
-/

set_option maxRecDepth 8192

namespace QStab.Examples.SteaneStandardNoGoAdequacy

open QStab QStab.QClifford QStab.QClifford.PCC QStab.QClifford.Compile
open QStab.Examples.SteaneStandardNoGo

/-! ## The 13-qubit embedding of a 7-qubit data error -/

/-- Embed a 7-qubit error vector on the 13 compiled qubits (data on `0..6`, `I` on the six
NZ ancillas `7..12`). -/
def emb13 (E : Fin 7 → Pauli) : Fin 13 → Pauli :=
  fun q => if h : q.val < 7 then E ⟨q.val, h⟩ else Pauli.I

/-! ## Combinatorial no-go cores (finite kernel `decide`) -/

/-- A single-qubit fault: Pauli `P` on qubit `q`. -/
@[reducible] def single7 (q : Fin 7) (P : Pauli) : ErrorVec 7 :=
  fun q' => if q' = q then P else Pauli.I

/-- The restriction of an operator to a set of positions (the physical shape of a hook). -/
@[reducible] def restrictTo7 (E : ErrorVec 7) (S : List (Fin 7)) : ErrorVec 7 :=
  fun q => if q ∈ S then E q else Pauli.I

/-- The weight-2 suffix hook of stabilizer `i` when its last two CNOT targets are `c, d`. -/
@[reducible] def suffix2 (i : Fin 6) (c d : Fin 7) : ErrorVec 7 := restrictTo7 (steaneStabVec i) [c, d]

/-- **The spec-level no-go core (CSS Z-sector).**  For every *Z*-stabilizer `i` (`3 ≤ i`) and every
distinct support pair `{c,d}`, there is a completing single-`Z` fault at some qubit `q` such that
the embedded completed hook `emb13 (suffix2 i c d · single7 q Z)` centralizes every `steaneSpec`
stabilizer yet is not in the stabilizer group — a genuine `logicalFailure` residual.  Kernel-`decide`d
over the finite space.  (Verified numerically in `notes/steane_css_check.py`: every weight-2
restriction of every Z-stabilizer completes via a single `Z` to an undetected `Z`-logical.) -/
theorem steane_nogo_core_spec :
    ∀ (i : Fin 6), 3 ≤ i.val → ∀ (c d : Fin 7), c ≠ d →
      steaneStabVec i c ≠ Pauli.I → steaneStabVec i d ≠ Pauli.I →
      ∃ (q : Fin 7),
        Centralizer steaneSpec (emb13 (ErrorVec.mul (suffix2 i c d) (single7 q Pauli.Z))) ∧
        ¬ Stab steaneSpec (emb13 (ErrorVec.mul (suffix2 i c d) (single7 q Pauli.Z))) := by
  decide

/-- **Deliverable 3, Step 1: strengthened Z-sector core for gadget 5.**  Every distinct support
pair `{c,d}` of `steaneStabVec 5` (the hook gadget) has a completing single-`Z` fault at some qubit
`q` **outside** the gadget-5 support (`steaneStabVec 5 q = I`), still a `logicalFailure` residual.
Keeping `q` out of the suffix means the completing data-`Z` fault does not land on a hook qubit
(no pre-existing `Z` on `{c,d}`), so it is injectable in gadget 3/4.  Kernel-`decide`d. -/
theorem steane_nogo_core_gadget5 :
    ∀ (c d : Fin 7), c ≠ d →
      steaneStabVec (5 : Fin 6) c ≠ Pauli.I → steaneStabVec (5 : Fin 6) d ≠ Pauli.I →
      ∃ (q : Fin 7), steaneStabVec (5 : Fin 6) q = Pauli.I ∧
        Centralizer steaneSpec (emb13 (ErrorVec.mul (suffix2 (5 : Fin 6) c d) (single7 q Pauli.Z))) ∧
        ¬ Stab steaneSpec (emb13 (ErrorVec.mul (suffix2 (5 : Fin 6) c d) (single7 q Pauli.Z))) := by
  decide

/-- `dataVector steaneSpec es = es.paulis` whenever `es.paulis` is an `emb13` embedding. -/
theorem dataVector_of_emb13 (es : ErrorState 13) (F : Fin 7 → Pauli)
    (hesdata : es.paulis = emb13 F) :
    dataVector steaneSpec es = emb13 F := by
  funext j
  simp only [dataVector, steaneSpec, hesdata]
  by_cases h : j.val < 7
  · simp [h]
  · simp only [emb13, dif_neg h]; simp [h]

/-- **Bridge.**  An error state whose data vector is exactly an embedded `Centralizer`-and-not-`Stab`
operator is a `logicalFailure` for `steaneSpec`. -/
theorem logicalFailure_of_core_spec
    (F : Fin 7 → Pauli) (es : ErrorState 13)
    (hcent : Centralizer steaneSpec (emb13 F))
    (hstab : ¬ Stab steaneSpec (emb13 F))
    (hesdata : es.paulis = emb13 F) :
    logicalFailure steaneSpec es := by
  have hdv := dataVector_of_emb13 es F hesdata
  exact ⟨hdv ▸ hcent, hdv ▸ hstab⟩

/-! ## Honest circuit decomposition into the six NZ gadget blocks -/

/-- **The compiled Steane Standard circuit is the concatenation of its six NZ gadget blocks.**
Gadget `i` (measuring `steaneStabVec i` under `order i`) sits at helper start `i`; gadget `0` is
first in the fault-location stream, gadget `5` last.  This is the object peeled by
`runFScript_append`. -/
theorem steaneStandardCircuit_decompose (order : Fin 6 → RuleSchedule 7)
    (h0 : 0 + helperCount Scheme.NZ (order 0) ≤ 6)
    (h1 : 1 + helperCount Scheme.NZ (order 1) ≤ 6)
    (h2 : 2 + helperCount Scheme.NZ (order 2) ≤ 6)
    (h3 : 3 + helperCount Scheme.NZ (order 3) ≤ 6)
    (h4 : 4 + helperCount Scheme.NZ (order 4) ≤ 6)
    (h5 : 5 + helperCount Scheme.NZ (order 5) ≤ 6) :
    (steaneStandardCircuit order : FCircuit (7 + 6)) =
      compileGadgetBlock .NZ (order 0) 0 h0 ++
      (compileGadgetBlock .NZ (order 1) 1 h1 ++
       (compileGadgetBlock .NZ (order 2) 2 h2 ++
        (compileGadgetBlock .NZ (order 3) 3 h3 ++
         (compileGadgetBlock .NZ (order 4) 4 h4 ++
          (compileGadgetBlock .NZ (order 5) 5 h5 ++ []))))) :=
  rfl

/-! ## `runFScript` clean-propagation primitives -/

/-- **All-`none` script = clean propagation.**  A script with no injections reduces a `runFScript`
run to the plain (fault-erased) circuit propagation, with fault count `0`.  This is the primitive
that peels a fault-free gadget block off the front (or back) of the full run. -/
theorem runFScript_allNone {nq : Nat} :
    ∀ (fc : FCircuit nq) (script : List (Option Pauli)) (es : ErrorState nq),
      (∀ o ∈ script, o = none) →
      runFScript fc script es = (propagateCircuit (eraseFaults fc) es, 0) := by
  intro fc
  induction fc with
  | nil => intro script es _; simp [runFScript, eraseFaults, propagateCircuit]
  | cons i rest ih =>
      intro script es hnone
      cases i with
      | gate g =>
          simp only [runFScript, eraseFaults, propagateCircuit]
          exact ih script (propagateGate g es) hnone
      | errLoc q =>
          cases script with
          | nil => simp only [runFScript, eraseFaults]; exact ih [] es (by simp)
          | cons o s' =>
              have ho : o = none := hnone o (by simp)
              subst ho
              simp only [runFScript, eraseFaults]
              exact ih s' es (fun x hx => hnone x (by simp [hx]))

/-- `injCount slots [] = 0` (an empty injection list injects nothing). -/
theorem injCount_nil {nq : Nat} (slots : List (ScheduledPauli nq)) :
    injCount slots [] = 0 := by
  induction slots with
  | nil => rfl
  | cons s rest ih => simp [injCount, ih]

/-- **One gadget block, no injection, on a commuting datum.**  Running an NZ gadget block under its
zero-injection block script (`blockScript slots []`), starting from a detector-quiet state whose
data agrees with `E` off the ancilla and whose schedule parity against `E` is even: the data is
preserved off the ancilla, the ancilla is cleaned to `I`, every detector stays `false`, and the
fault count is `0`.  This is the fault-free pass of a gadget over an already-committed datum. -/
theorem runFScript_nzBlock_noInject {nq : Nat} (anc : Fin nq) (slots : List (ScheduledPauli nq))
    (E : Fin nq → Pauli) (es : ErrorState nq)
    (hne : ∀ slot ∈ slots, slot.qubit ≠ anc)
    (hnodup : (slots.map (·.qubit)).Nodup)
    (hdata : ∀ q, q ≠ anc → es.paulis q = E q)
    (hdet : ∀ s, es.detectors s = false)
    (heven : scheduleParityList slots E false = false) :
    (∀ q, q ≠ anc →
        (runFScript (nzBlock anc slots) (blockScript slots []) es).1.paulis q = E q) ∧
    (runFScript (nzBlock anc slots) (blockScript slots []) es).1.paulis anc = Pauli.I ∧
    (∀ s, (runFScript (nzBlock anc slots) (blockScript slots []) es).1.detectors s = false) ∧
    (runFScript (nzBlock anc slots) (blockScript slots []) es).2 = 0 := by
  have hinj := injectE_all_false slots [] E (by intro b hb; simp at hb)
  have h := runFScript_nzBlock anc slots [] E es hne hnodup hdata hdet (by rw [hinj]; exact heven)
  rw [hinj] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, by rw [h4, injCount_nil]⟩

/-! ## The ancilla-hook `runFScript` machinery (the reusable CSS physics core)

The heart of the no-go: injecting a `Z` on a Z-gadget's ancilla *mid-ladder* (after `k` of its
data-controls have been coupled) deposits a `Z` on every *remaining* data control — the weight-`(w-k)`
`Z`-suffix hook — while leaving the ancilla carrying `Z` (so its own `measZ`, which reads
`hasXComp = false` of a `Z`, stays quiet).  These lemmas realise that at the concrete `runFScript`
fault-script level (kernel semantics, no `decide`), for the bare-CNOT Z-parity chain a Z-gadget
compiles to.  They are code-agnostic and reusable. -/

/-- errLoc count of a bare-CNOT Z-parity chain: two per CNOT (data control + ancilla). -/
theorem errLocCount_cnotChain {nq : Nat} (anc : Fin nq) :
    ∀ (qs : List (Fin nq)), (∀ q ∈ qs, q ≠ anc) →
      errLocCount ((qs.map (fun q => cnot q anc)).flatten) = 2 * qs.length := by
  intro qs
  induction qs with
  | nil => intro _; rfl
  | cons q rest ih =>
      intro hne
      have hqa : q ≠ anc := hne q (by simp)
      rw [List.map_cons, List.flatten_cons, errLocCount_append,
        show errLocCount (cnot q anc) = 2 from by simp [cnot, hqa, errLocCount],
        ih (fun q' hq' => hne q' (by simp [hq']))]
      simp [List.length_cons]; omega

/-- **The suffix hook injection.**  For a *nonempty* bare-CNOT chain, the script that idles the
first data-control errLoc (`none`) and injects `Z` on the ancilla errLoc of the head CNOT (`some Z`),
then idles the rest, reduces the run to: inject `Z` on the ancilla, then clean-propagate the whole
chain; fault count `1`. -/
theorem suffix_hook_cons {nq : Nat} (anc : Fin nq) (q : Fin nq) (rest : List (Fin nq))
    (hqa : q ≠ anc) (es : ErrorState nq) (m : Nat) :
    runFScript (((q :: rest).map (fun q => cnot q anc)).flatten)
        (none :: some Pauli.Z :: List.replicate m none) es
      = (propagateCircuit (eraseFaults (((q :: rest).map (fun q => cnot q anc)).flatten))
          (es.inject anc Pauli.Z), 1) := by
  rw [show ((q :: rest).map (fun q => cnot q anc)).flatten =
        cnot q anc ++ (rest.map (fun q => cnot q anc)).flatten from by
        simp [List.map_cons, List.flatten_cons]]
  rw [show cnot q anc = [FInstr.errLoc q, FInstr.errLoc anc, FInstr.gate (Gate.cnot q anc hqa)] from by
        simp [cnot, hqa]]
  show runFScript ([FInstr.errLoc anc, FInstr.gate (Gate.cnot q anc hqa)] ++
        (rest.map (fun q => cnot q anc)).flatten) (some Pauli.Z :: List.replicate m none) es = _
  simp only [List.cons_append, runFScript, if_neg (show Pauli.Z ≠ Pauli.I by decide), List.nil_append]
  rw [runFScript_allNone _ _ _ (by intro o ho; simp [List.mem_replicate] at ho; exact ho.2)]
  simp only [eraseFaults, propagateCircuit]

/-- The full hook script: `2k` idles (skip the first `k` CNOTs), then `none :: some Z` (idle the
`(k+1)`-th data control, inject `Z` on its ancilla), then `m` idles. -/
def hookScript (k m : Nat) : List (Option Pauli) :=
  List.replicate (2*k) none ++ (none :: some Pauli.Z :: List.replicate m none)

/-- **Ancilla-hook chain run.**  Running the bare-CNOT chain under `hookScript k m` (with `k` in
range) equals: clean-propagate the first `k` CNOTs (they see no fault), then run the remaining
chain under the head-injection script.  The composition law that peels the fault-free prefix. -/
theorem runFScript_cnotChain_hook {nq : Nat} (anc : Fin nq) (qs : List (Fin nq))
    (hne : ∀ q ∈ qs, q ≠ anc) (k m : Nat) (hk : k < qs.length) (es : ErrorState nq) :
    runFScript ((qs.map (fun q => cnot q anc)).flatten) (hookScript k m) es
      = ((runFScript (((qs.drop k).map (fun q => cnot q anc)).flatten)
            (none :: some Pauli.Z :: List.replicate m none)
            (propagateCircuit (eraseFaults (((qs.take k).map (fun q => cnot q anc)).flatten)) es)).1,
         (runFScript (((qs.drop k).map (fun q => cnot q anc)).flatten)
            (none :: some Pauli.Z :: List.replicate m none)
            (propagateCircuit (eraseFaults (((qs.take k).map (fun q => cnot q anc)).flatten)) es)).2) := by
  have hsplit : (qs.map (fun q => cnot q anc)).flatten =
      ((qs.take k).map (fun q => cnot q anc)).flatten ++
        ((qs.drop k).map (fun q => cnot q anc)).flatten := by
    conv_lhs => rw [← List.take_append_drop k qs]
    rw [List.map_append, List.flatten_append]
  have hpreEC : errLocCount (((qs.take k).map (fun q => cnot q anc)).flatten) = 2 * k := by
    rw [errLocCount_cnotChain anc (qs.take k) (fun q' hq' => hne q' (List.mem_of_mem_take hq'))]
    congr 1; rw [List.length_take]; omega
  rw [hsplit, runFScript_append]
  have hpre_none : ∀ o ∈ (List.replicate (2*k) none : List (Option Pauli)), o = none := by
    intro o ho; simp [List.mem_replicate] at ho; exact ho.2
  have htake : runFScript (((qs.take k).map (fun q => cnot q anc)).flatten) (hookScript k m) es
      = (propagateCircuit (eraseFaults (((qs.take k).map (fun q => cnot q anc)).flatten)) es, 0) := by
    rw [hookScript, runFScript_take_errLoc _ (List.replicate (2*k) none) _ es (by rw [hpreEC]; simp)]
    exact runFScript_allNone _ _ _ hpre_none
  rw [htake]
  simp only [Nat.zero_add]
  have hdrop : (hookScript k m).drop (errLocCount (((qs.take k).map (fun q => cnot q anc)).flatten))
      = none :: some Pauli.Z :: List.replicate m none := by
    rw [hpreEC, hookScript, List.drop_append_of_le_length (by simp)]
    simp
  rw [hdrop]

/-- **The chain hook residual.**  Injecting `Z` on the ancilla and clean-propagating a bare-CNOT
chain over data qubits `ps` (initially clean on `ps`, ancilla clean) leaves `Z` on the ancilla and
`Z` on every qubit of `ps` (`zPart Z = Z` on every control), identity elsewhere.  This is the
weight-`|ps|` `Z`-suffix hook. -/
theorem cnotChain_hook_residual {nq : Nat} (anc : Fin nq) (ps : List (Fin nq))
    (hanc : anc ∉ ps) (hnd : ps.Nodup) (es : ErrorState nq)
    (hesA : es.paulis anc = Pauli.I) (hesQ : ∀ q ∈ ps, es.paulis q = Pauli.I) (i : Fin nq) :
    (propagateCircuit (eraseFaults ((ps.map (fun q => cnot q anc)).flatten))
        (es.inject anc Pauli.Z)).paulis i
      = if i = anc then Pauli.Z else if i ∈ ps then Pauli.Z else (es.inject anc Pauli.Z).paulis i := by
  have hinjA : (es.inject anc Pauli.Z).paulis anc = Pauli.Z := by simp [ErrorState.inject, hesA]
  have hinjQ : ∀ q ∈ ps, (es.inject anc Pauli.Z).paulis q = Pauli.I := by
    intro q hq
    have hqa : q ≠ anc := fun h => hanc (h ▸ hq)
    simp [ErrorState.inject, hqa, hesQ q hq]
  rw [propagate_nzCnotChain_anc anc Pauli.Z ps hanc hnd (es.inject anc Pauli.Z) hinjA hinjQ i, zPart_Z]

/-! ## The completing data-`Z` fault (Z-slot injection)

The existing `runFScript_nzBlock` machinery models *data-`X`* injections (the positive reach
witness).  The pure-`Z` no-go attack needs a *data-`Z`* completing fault.  These lemmas supply it:
a `Z` on a CNOT control (a `Z`-slot's data qubit) stays on the control, so a mid-gadget data-`Z`
fault survives as `Z` on that qubit, leaves the ancilla untouched, and flips no detector. -/

theorem xPart_pauliMul_Z (p : Pauli) : xPart (pauliMul Pauli.Z p) = xPart p := by cases p <;> rfl
theorem pauliMul_I_left (p : Pauli) : pauliMul Pauli.I p = p := by cases p <;> rfl

theorem inject_paulis_self {nq : Nat} (es : ErrorState nq) (q : Fin nq) (p : Pauli) :
    (es.inject q p).paulis q = pauliMul p (es.paulis q) := by
  show (if q = q then pauliMul p (es.paulis q) else es.paulis q) = _; rw [if_pos rfl]

theorem inject_paulis_ne {nq : Nat} (es : ErrorState nq) (q i : Fin nq) (p : Pauli) (h : i ≠ q) :
    (es.inject q p).paulis i = es.paulis i := by
  show (if i = q then pauliMul p (es.paulis i) else es.paulis i) = _; rw [if_neg h]

/-- A CNOT acts as the identity on an error state whose control has no X-component and whose
target has no Z-component. -/
theorem propagateGate_cnot_id {nq : Nat} (c t : Fin nq) (h : c ≠ t) (X : ErrorState nq)
    (hc : xPart (X.paulis c) = Pauli.I) (ht : zPart (X.paulis t) = Pauli.I) :
    propagateGate (Gate.cnot c t h) X = X := by
  have hf : (propagateGate (Gate.cnot c t h) X).paulis = X.paulis := by
    funext i
    show (if i = t then pauliMul (xPart (X.paulis c)) (X.paulis t)
          else if i = c then pauliMul (zPart (X.paulis t)) (X.paulis c) else X.paulis i) = X.paulis i
    by_cases hit : i = t
    · subst hit; rw [if_pos rfl, hc, pauliMul_I_left]
    · rw [if_neg hit]; by_cases hic : i = c
      · subst hic; rw [if_pos rfl, ht, pauliMul_I_left]
      · rw [if_neg hic]
  show (⟨(propagateGate (Gate.cnot c t h) X).paulis, X.measFlips, X.detectors, X.detectorCursor⟩
        : ErrorState nq) = X
  rw [hf]

/-- **Deliverable 1: Z-slot data-fault.**  Running a Z-kind slot's gadget with a data-`Z` fault
(script `[some Z, none]`) on a state whose ancilla is clean and whose data qubit carries no
X-component leaves exactly `Z` on the data qubit (`es.inject slot.qubit Z`) — ancilla untouched,
detectors/cursor preserved (both via `inject`), and fault count 1. -/
theorem runFScript_zSlot_Zdata {nq : Nat} (anc : Fin nq) (slot : ScheduledPauli nq)
    (hk : slot.kind = XZPauli.Z) (hne : slot.qubit ≠ anc) (es : ErrorState nq)
    (hanc : es.paulis anc = Pauli.I) (hq : xPart (es.paulis slot.qubit) = Pauli.I) :
    runFScript (zParitySlot anc slot) [some Pauli.Z, none] es
      = (es.inject slot.qubit Pauli.Z, 1) := by
  have hcnot : zParitySlot anc slot
      = [FInstr.errLoc slot.qubit, FInstr.errLoc anc, FInstr.gate (Gate.cnot slot.qubit anc hne)] := by
    simp only [zParitySlot, hk, cnot, dif_neg hne]
  rw [hcnot]
  simp only [runFScript, if_neg (show Pauli.Z ≠ Pauli.I by decide)]
  refine Prod.ext ?_ rfl
  refine propagateGate_cnot_id slot.qubit anc hne _ ?_ ?_
  · rw [inject_paulis_self, xPart_pauliMul_Z, hq]
  · rw [inject_paulis_ne es slot.qubit anc Pauli.Z (Ne.symm hne), hanc]; rfl

/-! ## Deliverable 2: the Z-gadget block lift over a `pre ++ ⟨.Z,q⟩ :: post` split -/

/-- **Deliverable 2.1: Z-only no-fault identity.**  A fault-free Z-slot chain leaves the state
unchanged, given a clean ancilla and X-free scheduled data qubits (each CNOT is trivial). -/
theorem propagateCircuit_zParitySlots_Zonly {nq : Nat} (anc : Fin nq) :
    ∀ (slots : List (ScheduledPauli nq)) (es : ErrorState nq),
      (∀ s ∈ slots, s.kind = XZPauli.Z) → (∀ s ∈ slots, s.qubit ≠ anc) →
      es.paulis anc = Pauli.I → (∀ s ∈ slots, xPart (es.paulis s.qubit) = Pauli.I) →
      propagateCircuit (eraseFaults (zParitySlotsCircuit anc slots)) es = es := by
  intro slots
  induction slots with
  | nil =>
    intro es _ _ _ _
    simp only [zParitySlotsCircuit, List.map_nil, List.flatten_nil, eraseFaults_nil, propagateCircuit]
  | cons slot rest ih =>
    intro es hk hne hanc hx
    rw [zParitySlotsCircuit_cons, eraseFaults_append, QHL.Target.propagateCircuit_append]
    have hslotk : slot.kind = XZPauli.Z := hk slot (List.mem_cons.mpr (Or.inl rfl))
    have hslotne : slot.qubit ≠ anc := hne slot (List.mem_cons.mpr (Or.inl rfl))
    have hslotx : xPart (es.paulis slot.qubit) = Pauli.I := hx slot (List.mem_cons.mpr (Or.inl rfl))
    have hid : propagateCircuit (eraseFaults (zParitySlot anc slot)) es = es := by
      have hz : zParitySlot anc slot = cnot slot.qubit anc := by simp only [zParitySlot, hslotk]
      rw [hz, cnot, dif_neg hslotne]
      simp only [eraseFaults_errLoc, eraseFaults_gate, eraseFaults_nil, propagateCircuit]
      exact propagateGate_cnot_id slot.qubit anc hslotne es hslotx (by rw [hanc]; rfl)
    rw [hid]
    exact ih es (fun s hs => hk s (List.mem_cons.mpr (Or.inr hs)))
      (fun s hs => hne s (List.mem_cons.mpr (Or.inr hs))) hanc
      (fun s hs => hx s (List.mem_cons.mpr (Or.inr hs)))

theorem zParitySlotsCircuit_append {nq : Nat} (anc : Fin nq) (a b : List (ScheduledPauli nq)) :
    zParitySlotsCircuit anc (a ++ b) = zParitySlotsCircuit anc a ++ zParitySlotsCircuit anc b := by
  simp only [zParitySlotsCircuit, List.map_append, List.flatten_append]

/-- A fault-free (all-`none`) run of a Z-only slot chain returns the state unchanged, count 0. -/
theorem runFScript_zParitySlots_none {nq : Nat} (anc : Fin nq) (slots : List (ScheduledPauli nq))
    (script : List (Option Pauli)) (es : ErrorState nq) (hnone : ∀ o ∈ script, o = none)
    (hk : ∀ s ∈ slots, s.kind = XZPauli.Z) (hne : ∀ s ∈ slots, s.qubit ≠ anc)
    (hanc : es.paulis anc = Pauli.I) (hx : ∀ s ∈ slots, xPart (es.paulis s.qubit) = Pauli.I) :
    runFScript (zParitySlotsCircuit anc slots) script es = (es, 0) := by
  rw [runFScript_allNone _ _ _ hnone,
    propagateCircuit_zParitySlots_Zonly anc slots es hk hne hanc hx]

theorem drop_replicate_none (n : Nat) (r : List (Option Pauli)) :
    (List.replicate n none ++ r).drop n = r := by
  have h : (List.replicate n (none : Option Pauli) ++ r).drop
      (List.replicate n (none : Option Pauli)).length = r := List.drop_left
  rwa [List.length_replicate] at h

/-- Run a Z-only chain reading an all-`none` prefix of length `errLocCount`, ignoring the tail. -/
theorem runFScript_Zchain_none_pre {nq : Nat} (anc : Fin nq) (slots : List (ScheduledPauli nq))
    (es : ErrorState nq) (tail : List (Option Pauli))
    (hk : ∀ s ∈ slots, s.kind = XZPauli.Z) (hne : ∀ s ∈ slots, s.qubit ≠ anc)
    (hanc : es.paulis anc = Pauli.I) (hx : ∀ s ∈ slots, xPart (es.paulis s.qubit) = Pauli.I) :
    runFScript (zParitySlotsCircuit anc slots)
      (List.replicate (errLocCount (zParitySlotsCircuit anc slots)) none ++ tail) es = (es, 0) := by
  rw [runFScript_take_errLoc _ _ tail es (le_of_eq (List.length_replicate ..).symm)]
  exact runFScript_zParitySlots_none anc slots _ es
    (fun o ho => List.eq_of_mem_replicate ho) hk hne hanc hx

theorem drop2_someZ_none (r : List (Option Pauli)) :
    ([some Pauli.Z, none] ++ r).drop 2 = r := rfl

/-- **Deliverable 2.2: the runFScript split lemma.**  Over `pre ++ ⟨.Z,q⟩ :: post`, with all
scheduled data qubits X-free and the ancilla clean, the script that idles `pre`, fires one data-`Z`
at `q`, and idles `post` returns `(es.inject q Z, 1)`. -/
theorem runFScript_zParitySlots_split {nq : Nat} (anc : Fin nq)
    (pre post : List (ScheduledPauli nq)) (q : Fin nq) (es : ErrorState nq)
    (hk : ∀ s ∈ pre ++ (⟨XZPauli.Z, q⟩ : ScheduledPauli nq) :: post, s.kind = XZPauli.Z)
    (hne : ∀ s ∈ pre ++ (⟨XZPauli.Z, q⟩ : ScheduledPauli nq) :: post, s.qubit ≠ anc)
    (hanc : es.paulis anc = Pauli.I)
    (hx : ∀ s ∈ pre ++ (⟨XZPauli.Z, q⟩ : ScheduledPauli nq) :: post,
        xPart (es.paulis s.qubit) = Pauli.I) :
    runFScript (zParitySlotsCircuit anc (pre ++ (⟨XZPauli.Z, q⟩ : ScheduledPauli nq) :: post))
      (List.replicate (errLocCount (zParitySlotsCircuit anc pre)) none ++ [some Pauli.Z, none] ++
        List.replicate (errLocCount (zParitySlotsCircuit anc post)) none) es
      = (es.inject q Pauli.Z, 1) := by
  have hmid : (⟨XZPauli.Z, q⟩ : ScheduledPauli nq) ∈
      pre ++ (⟨XZPauli.Z, q⟩ : ScheduledPauli nq) :: post :=
    List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hqne : q ≠ anc := hne _ hmid
  have hqx : xPart (es.paulis q) = Pauli.I := hx _ hmid
  have hpreK : ∀ s ∈ pre, s.kind = XZPauli.Z := fun s hs => hk s (List.mem_append.mpr (Or.inl hs))
  have hpreNe : ∀ s ∈ pre, s.qubit ≠ anc := fun s hs => hne s (List.mem_append.mpr (Or.inl hs))
  have hpreX : ∀ s ∈ pre, xPart (es.paulis s.qubit) = Pauli.I :=
    fun s hs => hx s (List.mem_append.mpr (Or.inl hs))
  have hpostMem : ∀ s ∈ post, s ∈ pre ++ (⟨XZPauli.Z, q⟩ : ScheduledPauli nq) :: post :=
    fun s hs => List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hs)))
  have hpostK : ∀ s ∈ post, s.kind = XZPauli.Z := fun s hs => hk s (hpostMem s hs)
  have hpostNe : ∀ s ∈ post, s.qubit ≠ anc := fun s hs => hne s (hpostMem s hs)
  have hpostX : ∀ s ∈ post, xPart (es.paulis s.qubit) = Pauli.I := fun s hs => hx s (hpostMem s hs)
  have hIanc : (es.inject q Pauli.Z).paulis anc = Pauli.I := by
    rw [inject_paulis_ne es q anc Pauli.Z (Ne.symm hqne), hanc]
  have hIx : ∀ s ∈ post, xPart ((es.inject q Pauli.Z).paulis s.qubit) = Pauli.I := by
    intro s hs
    by_cases h : s.qubit = q
    · rw [h, inject_paulis_self, xPart_pauliMul_Z, hqx]
    · rw [inject_paulis_ne es q s.qubit Pauli.Z h]; exact hpostX s hs
  have hqneP : (⟨XZPauli.Z, q⟩ : ScheduledPauli nq).qubit ≠ anc := hqne
  have hqxP : xPart (es.paulis (⟨XZPauli.Z, q⟩ : ScheduledPauli nq).qubit) = Pauli.I := hqx
  have hELC : errLocCount (zParitySlot anc (⟨XZPauli.Z, q⟩ : ScheduledPauli nq)) = 2 := by
    rw [errLocCount_zParitySlot anc _ hqneP]; rfl
  have hmidRun : runFScript (zParitySlot anc (⟨XZPauli.Z, q⟩ : ScheduledPauli nq)
        ++ zParitySlotsCircuit anc post)
      ([some Pauli.Z, none] ++ List.replicate (errLocCount (zParitySlotsCircuit anc post)) none) es
      = (es.inject q Pauli.Z, 1) := by
    rw [runFScript_append, hELC,
      runFScript_take_errLoc _ [some Pauli.Z, none] _ es (le_of_eq hELC),
      runFScript_zSlot_Zdata anc ⟨XZPauli.Z, q⟩ rfl hqneP es hanc hqxP, drop2_someZ_none,
      runFScript_zParitySlots_none anc post _ (es.inject q Pauli.Z)
        (fun o ho => List.eq_of_mem_replicate ho) hpostK hpostNe hIanc hIx]
    rfl
  rw [zParitySlotsCircuit_append, zParitySlotsCircuit_cons, List.append_assoc, runFScript_append,
    runFScript_Zchain_none_pre anc pre es _ hpreK hpreNe hanc hpreX, drop_replicate_none, hmidRun]
  rfl

theorem drop_left_none (l r : List (Option Pauli)) : (l ++ r).drop l.length = r := List.drop_left

/-- **Deliverable 2.3: the Z-gadget block wrapper.**  Running the full NZ gadget block
(prep0, the Z-slot chain, measZ) under the block script that idles prep0, fires one data-`Z` at
`q`, idles the rest, and idles measZ: `Z` lands on `q`, the (still-`I`) ancilla is re-measured,
count 1.  The `propagateGate (Gate.measZ anc)` head makes the quiet detector explicit (it reads
`hasXComp` of the `I` ancilla, i.e. `false`). -/
theorem runFScript_zBlock_Zfault {nq : Nat} (anc : Fin nq)
    (pre post : List (ScheduledPauli nq)) (q : Fin nq) (es : ErrorState nq)
    (hk : ∀ s ∈ pre ++ (⟨XZPauli.Z, q⟩ : ScheduledPauli nq) :: post, s.kind = XZPauli.Z)
    (hne : ∀ s ∈ pre ++ (⟨XZPauli.Z, q⟩ : ScheduledPauli nq) :: post, s.qubit ≠ anc)
    (hx : ∀ s ∈ pre ++ (⟨XZPauli.Z, q⟩ : ScheduledPauli nq) :: post,
        xPart (es.paulis s.qubit) = Pauli.I) :
    runFScript (nzBlock anc (pre ++ (⟨XZPauli.Z, q⟩ : ScheduledPauli nq) :: post))
      ([none] ++ ((List.replicate (errLocCount (zParitySlotsCircuit anc pre)) none ++
        [some Pauli.Z, none] ++ List.replicate (errLocCount (zParitySlotsCircuit anc post)) none)
        ++ [none])) es
      = (propagateGate (Gate.measZ anc)
          ((propagateGate (Gate.prepZero anc) es).inject q Pauli.Z), 1) := by
  set slots := pre ++ (⟨XZPauli.Z, q⟩ : ScheduledPauli nq) :: post with hslots
  set split := List.replicate (errLocCount (zParitySlotsCircuit anc pre)) none ++
    [some Pauli.Z, none] ++ List.replicate (errLocCount (zParitySlotsCircuit anc post)) none
    with hsplit
  set es' := propagateGate (Gate.prepZero anc) es with hes'
  have hmemZ : (⟨XZPauli.Z, q⟩ : ScheduledPauli nq) ∈ slots := by
    rw [hslots]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hanc' : es'.paulis anc = Pauli.I := by
    rw [hes']; show (if anc = anc then Pauli.I else es.paulis anc) = Pauli.I; rw [if_pos rfl]
  have hx' : ∀ s ∈ slots, xPart (es'.paulis s.qubit) = Pauli.I := by
    intro s hs
    have hsne : s.qubit ≠ anc := hne s hs
    have he : es'.paulis s.qubit = es.paulis s.qubit := by
      rw [hes']; show (if s.qubit = anc then Pauli.I else es.paulis s.qubit) = _; rw [if_neg hsne]
    rw [he]; exact hx s hs
  have hELC : errLocCount (zParitySlot anc (⟨XZPauli.Z, q⟩ : ScheduledPauli nq)) = 2 := by
    rw [errLocCount_zParitySlot anc _ (hne _ hmemZ)]; rfl
  have hEL : errLocCount (zParitySlotsCircuit anc slots) = split.length := by
    rw [hslots, hsplit, zParitySlotsCircuit_append, zParitySlotsCircuit_cons,
      errLocCount_append, errLocCount_append, hELC]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  have hd1 : List.drop (errLocCount (prep0 anc)) ([none] ++ (split ++ [none])) = split ++ [none] := by
    simp [prep0, errLocCount]
  have hd2 : List.drop (errLocCount (zParitySlotsCircuit anc slots)) (split ++ [none]) = [none] := by
    rw [hEL]; exact drop_left_none split [none]
  rw [nzBlock,
    show prep0 anc ++ zParitySlotsCircuit anc slots ++ flagMeasZ anc
      = prep0 anc ++ (zParitySlotsCircuit anc slots ++ flagMeasZ anc) from by rw [List.append_assoc],
    runFScript_append (prep0 anc),
    runFScript_take_errLoc (prep0 anc) [none] (split ++ [none]) es (by simp [prep0, errLocCount]),
    runFScript_prep0, ← hes', hd1,
    runFScript_append (zParitySlotsCircuit anc slots),
    runFScript_take_errLoc (zParitySlotsCircuit anc slots) split [none] es' (le_of_eq hEL),
    runFScript_zParitySlots_split anc pre post q es' hk hne hanc' hx', hd2, runFScript_flagMeasZ]
  rfl

/-! ## `ValidStandardSchedule` bookkeeping — the symbolic-order locators

These lemmas turn `hv : ValidStandardSchedule order` (each gadget's slots only *up to* a
permutation of its canonical support) into the concrete structural facts the parametric attack
needs, **symbolic in `order`** — no `decide` on the order, no enumeration of the `∏ (wᵢ!)` valid
circuits.  The only `decide`s are on *closed finite Steane support facts* (the canonical slot lists
of the fixed Z-stabilizers).  This discharges obligation (2) of the parametric assembly. -/

/-! ### Concrete canonical-slot facts for the Z-stabilizers (indices 3,4,5) -/

theorem canonicalSlots_Z_kind (i : Fin 6) (hi : 3 ≤ i.val) :
    ∀ s ∈ canonicalSlots i, s.kind = XZPauli.Z := by
  fin_cases i <;> first | (exact absurd hi (by decide)) | decide

theorem canonicalSlots_len (i : Fin 6) (hi : 3 ≤ i.val) : (canonicalSlots i).length = 4 := by
  fin_cases i <;> first | (exact absurd hi (by decide)) | decide

theorem canonicalSlots_nodup_q (i : Fin 6) (hi : 3 ≤ i.val) :
    ((canonicalSlots i).map (·.qubit)).Nodup := by
  fin_cases i <;> first | (exact absurd hi (by decide)) | decide

theorem canonicalSlots_supp (i : Fin 6) (hi : 3 ≤ i.val) :
    ∀ s ∈ canonicalSlots i, steaneStabVec i s.qubit ≠ Pauli.I := by
  fin_cases i <;> first | (exact absurd hi (by decide)) | decide

/-! ### Transported to a valid schedule's actual slot list (via `List.Perm`, symbolic in `order`) -/

/-- Every slot the schedule assigns to a Z-gadget is a `Z`-slot. -/
theorem order_Z_kind {order : Fin 6 → RuleSchedule 7} (hv : ValidStandardSchedule order)
    (i : Fin 6) (hi : 3 ≤ i.val) : ∀ s ∈ (order i).slots, s.kind = XZPauli.Z :=
  fun s hs => canonicalSlots_Z_kind i hi s ((hv i).mem_iff.mp hs)

/-- A Z-gadget's schedule couples exactly four qubits. -/
theorem order_len {order : Fin 6 → RuleSchedule 7} (hv : ValidStandardSchedule order)
    (i : Fin 6) (hi : 3 ≤ i.val) : (order i).slots.length = 4 := by
  rw [(hv i).length_eq]; exact canonicalSlots_len i hi

/-- The coupled qubits are distinct. -/
theorem order_nodup_q {order : Fin 6 → RuleSchedule 7} (hv : ValidStandardSchedule order)
    (i : Fin 6) (hi : 3 ≤ i.val) : ((order i).slots.map (·.qubit)).Nodup :=
  ((hv i).map (·.qubit)).nodup_iff.mpr (canonicalSlots_nodup_q i hi)

/-- Every coupled qubit is in the stabilizer's support. -/
theorem order_supp {order : Fin 6 → RuleSchedule 7} (hv : ValidStandardSchedule order)
    (i : Fin 6) (hi : 3 ≤ i.val) : ∀ s ∈ (order i).slots, steaneStabVec i s.qubit ≠ Pauli.I :=
  fun s hs => canonicalSlots_supp i hi s ((hv i).mem_iff.mp hs)

/-! ### The two locators the pure-Z attack consumes -/

/-- A length-4 list splits into its four elements. -/
theorem list_len4 {α} (l : List α) (h : l.length = 4) : ∃ a b c d, l = [a, b, c, d] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at h <;>
    first | omega | exact ⟨a, b, c, d, rfl⟩

/-- **Last-two locator for gadget 5** (the hook gadget, `Z{3,4,5,6}`).  For *any* valid schedule,
its slot list ends in two `Z`-slots on distinct support qubits `c, d` — the weight-2 suffix the
ancilla hook deposits.  Symbolic in `order`. -/
theorem last2_locator {order : Fin 6 → RuleSchedule 7} (hv : ValidStandardSchedule order) :
    ∃ (pre : List (ScheduledPauli 7)) (c d : Fin 7),
      (order 5).slots = pre ++ [⟨XZPauli.Z, c⟩, ⟨XZPauli.Z, d⟩] ∧ c ≠ d ∧
      steaneStabVec 5 c ≠ Pauli.I ∧ steaneStabVec 5 d ≠ Pauli.I := by
  have hlen : (order 5).slots.length = 4 := order_len hv 5 (by decide)
  have hkind := order_Z_kind hv 5 (by decide)
  have hnd := order_nodup_q hv 5 (by decide)
  have hsp := order_supp hv 5 (by decide)
  obtain ⟨a, b, c, d, he⟩ := list_len4 _ hlen
  have hmc : c ∈ (order 5).slots := by
    rw [he]; simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto
  have hmd : d ∈ (order 5).slots := by
    rw [he]; simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto
  have hck : c.kind = XZPauli.Z := hkind c hmc
  have hdk : d.kind = XZPauli.Z := hkind d hmd
  have hcq : c = ⟨XZPauli.Z, c.qubit⟩ := by rw [← hck]
  have hdq : d = ⟨XZPauli.Z, d.qubit⟩ := by rw [← hdk]
  refine ⟨[a, b], c.qubit, d.qubit, ?_, ?_, ?_, ?_⟩
  · rw [he]; rw [← hcq, ← hdq]; rfl
  · rw [he] at hnd
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false] at hnd
    tauto
  · exact hsp c hmc
  · exact hsp d hmd

/-- A located slot in a valid schedule's gadget-`i` list gives an explicit append split. -/
theorem slot_in_order {order : Fin 6 → RuleSchedule 7} (hv : ValidStandardSchedule order)
    (i : Fin 6) (q : Fin 7) (hmem : (⟨XZPauli.Z, q⟩ : ScheduledPauli 7) ∈ canonicalSlots i) :
    ∃ (pre post : List (ScheduledPauli 7)), (order i).slots = pre ++ ⟨XZPauli.Z, q⟩ :: post :=
  List.append_of_mem ((hv i).mem_iff.mpr hmem)

/-- **Z-cover / completing-fault locator.**  The three Steane Z-stabilizers cover all 7 data
qubits, so for every `q` some Z-gadget `i ∈ {3,4,5}` couples it, and that `{Z, q}` slot sits at a
locatable position in the valid schedule's gadget-`i` slot list — where the completing data-`Z`
fault is injected.  Symbolic in `order`. -/
theorem z_cover_locator {order : Fin 6 → RuleSchedule 7} (hv : ValidStandardSchedule order)
    (q : Fin 7) :
    ∃ (i : Fin 6), 3 ≤ i.val ∧
      ∃ (pre post : List (ScheduledPauli 7)),
        (order i).slots = pre ++ ⟨XZPauli.Z, q⟩ :: post := by
  fin_cases q
  · exact ⟨3, by decide, slot_in_order hv 3 _ (by decide)⟩
  · exact ⟨4, by decide, slot_in_order hv 4 _ (by decide)⟩
  · exact ⟨3, by decide, slot_in_order hv 3 _ (by decide)⟩
  · exact ⟨5, by decide, slot_in_order hv 5 _ (by decide)⟩
  · exact ⟨3, by decide, slot_in_order hv 3 _ (by decide)⟩
  · exact ⟨4, by decide, slot_in_order hv 4 _ (by decide)⟩
  · exact ⟨3, by decide, slot_in_order hv 3 _ (by decide)⟩

/-! ## The remaining obstacle for a fully parametric `StandardAdequacy steaneSpec`

The pieces above reduce the campaign to *assembling* a real 2-fault `runFScript` run of
`steaneStandardCircuit order` — for every valid `order` — whose final data residual is exactly a
completed hook `emb13 (suffix2 5 c d · single7 q Z)` (with `{c,d}` the last-two coupled qubits of
gadget 5's chain and `q` from `steane_nogo_core_spec`) and whose detectors are all `false`.

The two faults are:

* **the hook** — a `Z` on gadget 5's ancilla injected after its first `(w-2)` couplings, depositing
  the weight-2 `Z`-suffix hook `suffix2 5 c d` on its last two data controls (via
  `runFScript_cnotChain_hook` + `cnotChain_hook_residual`, wrapped through `prep0`/`measZ` by
  peeling the block with `runFScript_append` + `runFScript_allNone`; the ancilla carries `Z`, so
  gadget 5's own `measZ` reads `hasXComp Z = false`);
* **the completing `Z`** — on data qubit `q` (from `steane_nogo_core_spec`), injected at `q`'s
  coupling in whichever Z-gadget (`3`, `4`, or `5`) couples it (the three Z-stabilizers cover all
  7 qubits, so such a gadget exists).

**What remains (and why it is a genuine development, not a `sorry`).**  Two obligations survive:

1. **The global detector-quiet invariant.**  Every `measZ` across all six blocks must read `false`.
   For the X-gadgets (`0,1,2`) this is because they run *first on clean data*; for the Z-gadgets
   because a `Z` on a data control contributes `xPart Z = I` to the ancilla, and the injected
   ancilla `Z` has `hasXComp Z = false`.  Mechanising this parametrically requires threading an
   "every ancilla is X-free at its `measZ`" invariant through `runFScript`'s detector cursor across
   all six blocks — a multi-block induction (the X-gadget-first ordering is load-bearing).

2. **The `List.Perm` bookkeeping for the completing fault's position.**  *This is now proved*
   (`order_Z_kind`/`order_len`/`order_nodup_q`/`order_supp`, `last2_locator`, `z_cover_locator`
   above): from `hv : ValidStandardSchedule order` alone — symbolic in `order`, with `decide` used
   only on closed finite Steane support facts — we obtain gadget 5's last-two `Z`-suffix pair
   `{c,d}` and, for every data qubit `q`, a Z-gadget coupling it with an explicit slot-list append
   split.  What still remains under this heading is purely the *script alignment*: turning these
   append splits (`pre ++ … :: post`) into the `errLocCount`-indexed `runFScript` injection offsets
   and feeding them to the hook/measure peeling — mechanical, but not yet assembled.

Obligation (1) is the genuine remaining development; obligation (2)'s combinatorics is discharged.
Both are handled honestly — no `sorry`, no axiom, no weakened theorem.  The
concrete `steaneSpec_canonical_dangerousRun` in `SteaneStandardNoGo.lean` discharges the *canonical*
schedule at the real circuit level (kernel `decide`), and the machinery in this file is the reusable
core of the parametric assembly. -/

end QStab.Examples.SteaneStandardNoGoAdequacy
