/-!
# Milestone T (trees) — design deliverable (NO implementation)

The three-mandate audit converges here: make the **target-level distance argument a
checked syntactic certificate**, and the **lowering a fixed tree-to-tree conversion**.
This module is the design pass only (per the milestone: "the design gets its own review
first").  Nothing below is code; the identifiers named are the real ones so the plan is
auditable against the tree.

Prerequisites `F1` (spec alignment) and `F2` (reach script) are certificate *data* and are
needed regardless of T.

---

## (1) Trusted base enumeration — what `Safe` soundness rests on

The zero-trust story is only as strong as the base a malicious prover cannot touch.  Today
that base, followed from `vcgen_sound` outward, is exactly:

* **Kernel + `Prop` semantics** — Lean's type checker (axioms `propext`, `Classical.choice`,
  `Quot.sound` only).
* **The safety target** — `PCC/Basic.lean : Safe C spec` = `WellFormed C spec ∧ readout-
  disjoint ∧ (∀ i E, gadgetMeasFlip … = parity …) ∧ ToleratesFaultsΛ C (failure spec)
  (spec.d - 1) ∧ (∃ es, fcevalW spec.d C clean es ∧ failure spec es)`.
* **The failure predicate** — `failure`, `logicalFailure` (= `Centralizer ∧ ¬ Stab` over
  `dataVector`), `Centralizer`, `Stab`, `prodStab`, `vectorParity`, `undetected`,
  `allPostselectionFlagsZero`, `allFlagsZero`.  [PCC/Basic.lean — verifier-protected.]
* **The obligation generator** — `PCC/VCGen.lean : vcgen`, `GeneratedVCs`, `VCSlot.denote`
  (the *only* place a slot becomes a `Prop`), `DischargedVCs`, `VCGen`, and the soundness
  theorem `vcgen_sound : VCGen input → Safe input.program input.toCodeSpec`.
  [Verifier-protected region.]
* **The spec constructor** — `VCInput.ofPCC` / `toCodeSpec`; `fullProgramCodeSpec(D)` whose
  `stabilizer := scheduleRow (schedule i)` is derived from the *submitted program's own*
  schedules (a lying prover cannot smuggle different stabilizers).
* **The concrete evaluators** — `runFScript` + `runFScript_sound` (reach), `qceval` /
  `fcevalW` / `propagateCircuit` (the noise semantics), `denoteQC_circuitDistanceAny` and
  `VCInput.formulaReport_faithful` (the assertion-language faithfulness bridges).
* **The syndrome checker** — `SyndromeHoareCertificate.syn` + `hoare_sound_c` (the target
  `DerivC` tree-checker) for the `syn` slot.

**Gap (T deliverable):** `vcgen`'s `ftDistance` and `reach` slots are `Prop`s discharged by
*arbitrary Lean proofs*, not by certificate data fed to a small fixed checker.  Enumerating
this base in one file (this section) is deliverable (1); shrinking the base by replacing the
`ftDistance` proof with a checked `DistDeriv` is deliverables (2)–(3).

---

## (2) Target derivation-rule set — a proposed inductive `DistDeriv`

The target barrier argument is *already* structured — it is carried semantically by
`DistanceCertificate'` (`PCC/Basic.lean`):

    barrier : ErrorState nq → Nat
    programEq / wf / syn        -- the three discharged slots
    noUndetectedHook : ∀ i, NoUndetectedHook (spec.gadget i) spec barrier
    cancellation     : CancellationBenign C spec barrier
    dist             : ∀ es, logicalFailure spec es → spec.d ≤ barrier es
    reachScript / reachOk

and `certificate'_tolerates` proves `ToleratesFaultsΛ` from these fields.  These fields are
the *semantic* obligations; the `docs/` geometric-frontier derivation
(`surface_d3_nz_qclifford_geometric_hoare_certificate.json`, 227 nodes, Python-checked,
rules `L001–L004` / `H-LocalFaultFrontier` / `H-GateFrontier`, written "for the future proof
compiler") is the *syntactic* frontier tree for the same argument.

**Proposal.**  An inductive `DistDeriv C spec (barrier : ErrorState nq → ℕ)` whose leaves are
the frontier rules and whose checker `distCheck : DistDeriv → Bool` (small, fixed,
decide-free on the parametric path) reduces to the `DistanceCertificate'` fields:

* `DistDeriv.init`      ⟷ `init : barrier clean = 0`                          (leaf, `L001`)
* `DistDeriv.gateFront` ⟷ `preserve`/`H-GateFrontier` (barrier invariant under a gate)
* `DistDeriv.siteFront` ⟷ `step`/`H-LocalFaultFrontier` (`SiteSafeβ` at each errLoc site)
* `DistDeriv.noHook`    ⟷ `noUndetectedHook` (per-gadget, `L002`)
* `DistDeriv.cancel`    ⟷ `cancellation` = `CancellationBenign` (`L003`)
* `DistDeriv.floor`     ⟷ `dist : logicalFailure → spec.d ≤ barrier` (`L004`, the geometry
  floor — this is where `xLowerBoundByGeometryF` / `zLowerBoundByGeometryF` enter)

`distCheck`-soundness theorem: `distCheck cert = true → ToleratesFaultsΛ C (failure spec)
(spec.d - 1)` — a thin wrapper over `certificate'_tolerates`, moving the trust from
"arbitrary Lean proof of `ftDistance`" to "kernel-check of the fixed `distCheck` term".

**Design tension to resolve in review:** `dist`/`L004` is a *geometry* fact (row/column
counting), not a frontier-local rule; whether it stays a single leaf carrying the geometry
lemma, or is itself decomposed into a checked sub-derivation, is the main open rule-set
question.  Recommend: keep it a leaf initially (the geometry lemmas are already proven), and
revisit after F3's any-logical coverage lands.

---

## (3) Lowering compiler sketch — source `Certificate` → target `DistDeriv`

Today's lowering is one fixed meta-theorem (`etildeC_hoare_preservation`, CompCert-style,
proven once).  T replaces it with a rule-by-rule tree-to-tree function
`compileDist : SourceCertificate → DistDeriv` plus `compileDist_sound`.

**Source side.**  `surface_invariant_certificate` produces genuine `Certificate` /
`SyntacticBarrierContractCertificate` trees (source barrier `barrierInvF β L`).  Its
constructors (the barrier-contract leaves: `init`/`spread`/`logical`/`preserve`) are the
domain of `compileDist`.

**Prior art (salvageable).**  The retired Phase A–E stack under
`notes/retired-command-qhl/QStab/QHL/Compile/` is exactly a rule-by-rule lowering:

* `CompilationRules.lean` — `compileRule_skip/seq/conseq/t0/t1/t2/t3/meas` (transparent,
  `[propext]`-only inspectors) + `DerivCompilable` + `DerivStructural`.
* `CompileSound.lean` — `compile_sound : DerivCompilable → FHoare` by explicit case analysis
  (the pattern `compileDist_sound` should follow).
* `BarrierFHoare.lean` — the barrier-carrying FHoare bridge.

The salvage: `compileRule_*`'s *shape* (one transparent constructor per source rule, an
`Inspector` that is `[propext]`-only, `#eval`-reducible `count_*`) is the template.  What
must change: the target is `DistDeriv` (the barrier/distance argument), not the `syn`-level
`FHoareSkeleton`; and the lowering must thread the *barrier* (`compileFormula` already maps
`barrierInvF` across layers via `qstabBackend` → `qcliffordDataBackend`, so the barrier
symbol survives — the lowering carries the frontier structure, not a re-derivation).

**Non-negotiable (Rule 2):** `compileDist` must be a *function on trees*, never a
program-substitution; the `Formula` (`barrierInvF β L`) is re-interpreted by the backend,
never redefined.

---

## (4) Honest cost estimate (per piece)

* **(1) Trusted-base enumeration** — DONE in prose above; to make it a *checked* artifact
  (a Lean `#print axioms` sweep + a one-file `import`-graph of the protected region): ~0.5
  session.
* **(2) `DistDeriv` + `distCheck` + `distCheck_sound`** — the inductive + a `Bool` checker +
  the wrapper over `certificate'_tolerates`: ~1–1.5 sessions (the `floor`/`L004` leaf reuses
  landed geometry; the frontier leaves reuse `errLocsWithSuffix`/`SiteSafeβ`).
* **(3) `compileDist` + `compileDist_sound`** — the tree-to-tree function + soundness by
  structural case analysis, mirroring retired `compile_sound`: ~2–3 sessions (the barrier
  threading is the risk; `compileFormula`'s cross-layer identity de-risks it).
* **Total T** — ~4–5 sessions on top of `F1`+`F2` (which are prerequisites and independently
  scoped).  T does **not** change any verifier-protected file; it *shrinks* the trusted base
  by moving `ftDistance` from arbitrary-proof to checked-`DistDeriv`.

**Recommendation for the review pass:** settle the deliverable-(2) rule-set question (is
`L004`/`dist` one leaf or a sub-derivation?) before writing any `DistDeriv` code, since it
determines the checker's size and the `compileDist` case count.
-/
