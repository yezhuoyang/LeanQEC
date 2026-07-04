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

2. **The `List.Perm` bookkeeping for the completing fault's position.**  `ValidStandardSchedule`
   gives each gadget's slot list only up to permutation of the canonical support; locating `q`'s
   coupling slot (and gadget 5's last-two pair `{c,d}`) inside an arbitrary permuted order, and
   aligning the two injection scripts, is symbolic in `order` — neither a `decide` nor a finite
   enumeration (≈`(4!·3!·4!·4!·3!·4!)` valid circuits).

Both are deliberately left un-assumed here — no `sorry`, no axiom, no weakened theorem.  The
concrete `steaneSpec_canonical_dangerousRun` in `SteaneStandardNoGo.lean` discharges the *canonical*
schedule at the real circuit level (kernel `decide`), and the machinery in this file is the reusable
core of the parametric assembly. -/

end QStab.Examples.SteaneStandardNoGoAdequacy
