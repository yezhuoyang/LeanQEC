import QStab.Examples.FiveQubitStandardNoGo
import QStab.QClifford.Compile.NZReachCalculus

/-!
# Toward discharging `StandardAdequacy fqSpec` — reusable clean pieces

This file develops the circuit-level pieces needed to make `fiveQubit_standard_full_nogo`
unconditional.  Two ingredients are landed here, both axiom-clean and `decide`-checked:

* **`nogo_core_spec`** — the spec-level no-go core: every weight-2 suffix hook of any
  `[[5,1,3]]` stabilizer, completed by one single-qubit fault, embeds on the 9 compiled qubits
  to a genuine `logicalFailure`-shaped fact (`Centralizer fqSpec ∧ ¬ Stab fqSpec`).  This is the
  algebraic bridge from the finite combinatorial `nogo_core` to the PCC verifier's `fqSpec`
  predicates, bypassing any parity re-derivation.

* **`fiveQubitStandardCircuit_decompose`** — the honest decomposition of the compiled circuit into
  its four NZ gadget blocks (`compileGadgetBlock .NZ (order i) i _`), the target of the
  `runFScript_append` composition law.

The remaining obligation — assembling a real `runFScript` 2-fault run whose residual is exactly a
completed suffix hook — is the surviving-completing-fault fault-propagation campaign documented at
the end of this file.
-/

namespace QStab.Examples.FiveQubitStandardNoGoAdequacy

open QStab QStab.QClifford QStab.QClifford.PCC QStab.QClifford.Compile
open QStab.Examples.FiveQubitStandardNoGo QStab.Examples.FiveQubitNoGo

/-! ## The 9-qubit embedding of a 5-qubit data error -/

/-- Embed a 5-qubit error vector on the 9 compiled qubits (data on `0..4`, `I` on the four
NZ ancillas `5..8`). -/
def emb9 (E : Fin 5 → Pauli) : Fin 9 → Pauli :=
  fun q => if h : q.val < 5 then E ⟨q.val, h⟩ else Pauli.I

/-! ## The spec-level no-go core (finite kernel `decide`)

The combinatorial `nogo_core` lives in the 5-qubit `ErrorVec`/`ErrorVec.parity` world.  The PCC
verifier speaks `Centralizer fqSpec` (via `vectorParity` on the 9-qubit `fqEmb`) and `Stab fqSpec`.
Rather than prove a parity-notion bridge, we re-establish the entire completed-hook fact directly at
the `fqSpec` level over the finite `(i, c, d, q, P)` space. -/

/-- **The spec-level no-go core.**  For every stabilizer `i` and every distinct support pair
`{c,d}`, there is a completing single-qubit fault `(q, P)` such that the embedded completed hook
`emb9 (suffix2 i c d · single q P)` centralizes every `fqSpec` stabilizer yet is not in the
stabilizer group — a genuine `logicalFailure` residual.  Kernel-`decide`d over the finite space. -/
theorem nogo_core_spec :
    ∀ (i : Fin 4) (c d : Fin 5), c ≠ d → fqStab i c ≠ Pauli.I → fqStab i d ≠ Pauli.I →
      ∃ (q : Fin 5) (P : Pauli), P ≠ Pauli.I ∧
        Centralizer fqSpec (emb9 (ErrorVec.mul (suffix2 i c d) (single q P))) ∧
        ¬ Stab fqSpec (emb9 (ErrorVec.mul (suffix2 i c d) (single q P))) := by
  decide

/-- `dataVector fqSpec es = es.paulis` whenever `es.paulis` is an `emb9` embedding (its ancillas,
qubits `≥ 5`, are already `I`, and `fqSpec.isData` is exactly `· < 5`). -/
theorem dataVector_of_emb9 (es : ErrorState 9) (F : Fin 5 → Pauli)
    (hesdata : es.paulis = emb9 F) :
    dataVector fqSpec es = emb9 F := by
  funext j
  simp only [dataVector, fqSpec, hesdata]
  by_cases h : j.val < 5
  · simp [h]
  · simp only [emb9, dif_neg h]; simp [h]

/-- Packaged: the embedded completed hook is a `logicalFailure` for any error state whose data
vector is exactly that embedding (its ancillas being `I`). -/
theorem logicalFailure_of_nogo_core_spec
    (F : Fin 5 → Pauli) (es : ErrorState 9)
    (hcent : Centralizer fqSpec (emb9 F))
    (hstab : ¬ Stab fqSpec (emb9 F))
    (hesdata : es.paulis = emb9 F) :
    logicalFailure fqSpec es := by
  have hdv := dataVector_of_emb9 es F hesdata
  exact ⟨hdv ▸ hcent, hdv ▸ hstab⟩

/-! ## Honest circuit decomposition into the four NZ gadget blocks -/

/-- **The compiled five-qubit Standard circuit is the concatenation of its four NZ gadget blocks.**
Gadget `i` (measuring `fqStab i` under order `order i`) sits at helper start `i`; gadget `0` is
first in the fault-location stream, gadget `3` last.  This is the object peeled by
`runFScript_append`. -/
theorem fiveQubitStandardCircuit_decompose (order : Fin 4 → RuleSchedule 5)
    (h0 : 0 + helperCount Scheme.NZ (order 0) ≤ 4)
    (h1 : 1 + helperCount Scheme.NZ (order 1) ≤ 4)
    (h2 : 2 + helperCount Scheme.NZ (order 2) ≤ 4)
    (h3 : 3 + helperCount Scheme.NZ (order 3) ≤ 4) :
    (fiveQubitStandardCircuit order : FCircuit (5 + 4)) =
      compileGadgetBlock .NZ (order 0) 0 h0 ++
      (compileGadgetBlock .NZ (order 1) 1 h1 ++
       (compileGadgetBlock .NZ (order 2) 2 h2 ++
        (compileGadgetBlock .NZ (order 3) 3 h3 ++ []))) :=
  rfl

/-- Every valid Standard schedule's stabilizer-`i` slot list has the same multiset as the
canonical slots, hence its last-two coupled qubits are a distinct support pair — the pair the
gadget-3 hook is deposited on.  (Extracted from `ValidStandardSchedule` for the assembly.) -/
theorem valid_slots_perm (order : Fin 4 → RuleSchedule 5)
    (hv : ValidStandardSchedule order) (i : Fin 4) :
    List.Perm (order i).slots (canonicalSlots i) := hv i

/-! ## The remaining obstacle for `StandardAdequacy fqSpec` (the surviving-completing-fault campaign)

The pieces above reduce `StandardAdequacy fqSpec` to producing, for every valid `order`, a real
2-fault `runFScript` run of `fiveQubitStandardCircuit order` whose final data residual is exactly a
completed suffix hook `emb9 (suffix2 3 c d · single q P)` (with `{c,d}` the last-two coupled
qubits of `order 3`) and whose detectors are all `false`.

**Why this is not a short fault-propagation argument (numerically established, `notes/nogo_study.py`).**
The *first* fault (ancilla-`Z` mid-ladder in the LAST gadget) does deposit the weight-2 suffix hook
`suffix2 3 c d` on the data, keeps gadget-3's own detector quiet (a `Z` on the ancilla has no
`X`-component at `measZ`), and — being the last gadget — the hook is re-coupled by no later gadget,
so no later detector fires.  That half is a clean specialisation of `propagate_nzCnotChain_anc` /
`propagate_nzHSandwichChain_anc` (Z-slot / X-slot) and would be a tractable new lemma.

The *completing* fault is the wall.  The `nogo_core_spec` witness `q` is provably NOT always in
`support (fqStab 3)` (kernel `decide`), so it cannot be reached by any gadget-3 ancilla injection
(those only touch stab-3 support).  Exhaustive search (`notes/nogo_study.py`) confirms:

* NO 2-fault attack confined to gadget 3 exists for all schedules (`study7`);
* NO two-ancilla attack exists for all schedules (`study4`);
* NO gadget-3 window (two-suffix-hook) attack exists for all gadget-3 orderings (`study6`).

For the worst-case schedules the completing single-qubit fault must be injected at qubit `q`'s
*last coupling* — in a gadget `< 3` (chosen by the order) — and then propagate through the
remaining gadgets to the end.  Because the code is non-CSS, a residual Pauli on `q` re-coupled by a
later slot of the "wrong" kind flips that gadget's detector; keeping every detector quiet forces an
order-dependent kind-matching condition on `P` and on `q`'s later couplings.  Mechanising this — a
`runFScript`-level "single data fault injected at `q`'s last coupling survives the tail
detector-quiet, with `P`-kind matching every later slot on `q`" lemma, parametric over all valid
orders — is a genuine multi-hundred-line non-CSS fault-propagation development.  It is neither a
`decide` (the injection position and survival are symbolic in `order`) nor an enumeration (≈`24^4`
distinct valid circuits).  It is the honest next stage of the campaign and is deliberately left
un-assumed here (no `sorry`, no axiom, no weakened theorem) rather than papered over. -/

end QStab.Examples.FiveQubitStandardNoGoAdequacy
