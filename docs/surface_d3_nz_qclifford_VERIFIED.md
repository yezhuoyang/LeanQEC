# Surface-d3 NZ QClifford Verification Capstone

Run the full verification and regression suite with:

```bash
python tools/verify_all.py
```

The command exits 0 only if the QClifford Lean proof builds, the final Lean
theorem axiom sets are exactly `[propext, Classical.choice, Quot.sound]`, the
Python QClifford certificate checker accepts the real certificate, the
QClifford Lean/certificate correspondence checker accepts the real pair, and
all tampered copies are rejected.

## Exact QClifford Theorem

The authoritative kernel-checked exact-distance statement is
`QStab.QClifford.SurfaceD3Distance.surfaceD3_distance_exact_qclifford`.

```lean
theorem surfaceD3_tolerates_two_faults :
    ToleratesFaultsΛ C_NZ_D3 logicalFailure 2

theorem surfaceD3_reachable_three_fault_logical :
    exists es, fcevalW 3 C_NZ_D3 (ErrorState.clean 10) es /\
      logicalFailure es

theorem surfaceD3_distance_exact_qclifford :
    ToleratesFaultsΛ C_NZ_D3 logicalFailure 2 /\
      exists es, fcevalW 3 C_NZ_D3 (ErrorState.clean 10) es /\
        logicalFailure es
```

The lower-bound theorem is obtained through:

```lean
surfaceD3Deriv : FDeriv cleanPre C_NZ_D3 distPost
surfaceD3_hoare := fhoare_sound surfaceD3Deriv
surfaceD3_tolerates_two_faults :=
  toleratesFaultsΛ_of_hoare C_NZ_D3 logicalFailure 2 surfaceD3_hoare
```

so the proof uses the existing QClifford fault-Hoare logic and QClifford
`qceval`/`fcevalW`/`propagateGate` semantics, not the legacy Paper `HDeriv`
stack.

## Artifacts

- `QStab/QHL/Assertion/Syntax.lean` and
  `QStab/QHL/Assertion/Semantics.lean`: the single shared assertion language.
  QClifford does not introduce a parallel assertion syntax.  The existing
  `Formula`/`Term` language now has a small generic detector term and
  backend-parametric semantics through `AssertionBackend`; the old QStab
  interpretation is recovered by `qstabBackend`, while QClifford uses a
  backend that reads data residuals, `lambda`, and time-resolved detector
  slots from `QCState`.
- `QStab/QClifford/SurfaceD3Distance.lean`: authoritative QClifford circuit,
  `FDeriv` derivation, `ToleratesFaultsΛ` theorem, 3-fault reachability
  witness, and emitted QClifford-side code/schedule/bound JSON.
- `QStab/QClifford/PCC/Basic.lean`: foundational PCC kernel. It defines
  `CodeSpec`, `Safe`, `allFlagsZero`, generated VC predicates such as `WellFormed` and
  `SiteSafeβ`, `DistanceCertificate`, the generic `certificateDeriv : FDeriv ...`,
  and `certificate_sound : DistanceCertificate C spec -> Safe C spec`. It also
  defines the first-class detector combiner: `stabilizerReadout i` is a list
  of raw detector slots and `syndromeBit` is the XOR of exactly that list.  It
  also contains the detection-conditioned PCC skeleton
  `DistanceCertificate'`/`certificate_sound'`; the primed certificate requires
  a producer-supplied `CancellationBenign` proof that accepted
  detector-cancelling hook groups keep the barrier bounded by the actual fault
  count.
- `QStab/QClifford/PCC/VCGen.lean`: the lazy VC-generation boundary and the
  **bridge layer** that makes the shared QHL assertion language load-bearing
  for QClifford VCs.  It separates pure input syntax (`StabilizerSyntax`,
  `StabilizerCodeSyntax`, `ExtractionSyntax`, `VCInputSyntax`) from the
  interpreted backend (`StabilizerCodeSpec`, `ExtractionSpec`, and `VCInput`),
  defines `qcliffordBackend` (the `AssertionBackend` that maps `error` to
  `dataVector`, `spent` to `sigma.lambda`, and `detector k` to
  `sigma.es.detectors k`), and renders the generated assertions with the shared
  QHL formula syntax (`logicalAnyResidualF`, `allFlagsZeroF`, and
  `circuitDistanceAnyF`).

  The shared formulas stored in `VCFormulaReport` are **not decorative tags**:
  each is *proven equal* to the concrete QClifford obligation it claims to
  denote, under `Formula.denoteQC` (= `Formula.denoteWith qcliffordBackend`).
  The four bidirectional bridge theorems are:

  - `denoteQC_allFlagsZeroF`: `allFlagsZeroF` denotes `allFlagsZero`.
  - `denoteQC_logicalAnyResidual`: `logicalAnyResidualF .error` denotes
    `logicalFailure`.
  - `denoteQC_failureF`: `failureF` denotes `failure` (combines Bridges 1+2).
  - `denoteQC_circuitDistanceAny`: `circuitDistanceAnyF spec.d` denotes
    `logicalFailure sigma.es -> spec.d <= sigma.lambda`.

  `VCInput.formulaReport_faithful` packages all three report fields as a
  single conjunction of biconditionals, certified axiom-clean.
  `vcgen_safe_in_assertion_language` shows that accepted runs satisfy the
  distance formula in the assertion language, not just as a parallel claim
  but via the bridge.

  The Hoare skeleton (`FHoareSkeleton`, `frontierSkeleton`, `hoareSkeleton`)
  is a proof-free tag tree mirroring the shape of `frontierDeriv`.  It is
  **connected to `frontierDeriv`** via three grounding theorems:
  `frontierSkeleton_sound` (discharging `.step`/`.programEq`/`.preserve`
  constructs a genuine `FDeriv`), `hoareSkeleton_sound` (unconditional path),
  and `hoareSkeleton_sound'` (postselected path).  No claim that the skeleton
  is load-bearing is made that is not backed by one of these proofs.

  All bridge and skeleton-grounding theorems build with axioms exactly
  `[propext, Classical.choice, Quot.sound]` (verified by `#print axioms`
  in the file and checked by `tools/verify_all.py`).

  The file also defines the proof-free generated artifact
  `vcgen input : GeneratedVCs input`, whose output contains a syntactic
  `slots : List VCSlot` obligation list and the `hoare` skeleton, and proves
  `vcgen_sound : VCGen input -> Safe input.program input.toCodeSpec` by
  packaging producer discharges as the existing `DistanceCertificate` or
  `DistanceCertificate'` and applying `certificate_sound` or
  `certificate_sound'`.
- `QStab/QClifford/Compile/Calculus.lean`: explicit QClifford compilation
  calculus. It defines `Scheme`, `Schedule`, `AncillaConfig`, `flagMeasZ`,
  `rawMeasZ`, and `compileGadget`. For the NZ surface schedule it proves
  `compiledCircuit_eq_C_NZ_D3`, so the compiler fold emits exactly the
  existing concrete circuit. It also proves the Knill Z-side erasure theorem
  `erase_compileKnill_z_eq_knillCircuit`, tying the instrumented Knill
  compiler rule to the existing `QStab.QClifford.Knill.knillCircuit`.
- `QStab/QClifford/PCC/SurfaceD3.lean`: closed surface-d3 PCC client. It defines
  the explicit time-resolved flag-slot mapping `flagSlot i := i.val`
  plus the required ordered-slot proof, proves detector/stabilizer correctness, bridges the generic
  `Centralizer /\ not Stab` predicate to the surface geometry, fills every
  `DistanceCertificate` field, packages it as `surfaceD3VCGen`, and exports
  `surfaceD3_safe` through `vcgen_sound surfaceD3VCGen`.
- `QStab/QClifford/PCC/SurfaceD3Knill.lean`: closed Knill surface-d3 PCC
  client. It sets each `stabilizerReadout i` to the raw transversal
  measurement slots for that stabilizer, proves their XOR equals the
  stabilizer parity, reuses the surface geometry/barrier obligations, and
  exports `surfaceD3_knill_safe` through `vcgen_sound surfaceD3KnillVCGen`.
- `QStab/QClifford/PCC/SurfaceD3Shor.lean`: checked Shor surface-d3 PCC
  skeleton. It fixes the 41-qubit Shor-compiled surface circuit, the
  per-stabilizer XOR readouts, verifier post-selection slots, the reused
  surface barrier, and the exact remaining producer obligation
  `surfaceAcceptedBarrierBound`. It also contains the explicit accepted-bound
  ladder scaffold: closed L1/L3 rungs (`benign_spread_le`,
  `dangerous_branch_fires`, `dangerousSpread_subadditive`, and
  `benign_contribution_product_le_length`) plus the L4 bridge
  `surfaceAcceptedBarrierBound_of_ladder`. It intentionally does not export
  `surfaceD3_shor_safe` until the remaining L0/L2-style run decomposition and
  dangerous-hook grouping theorem is proved.
- `QStab/Paper/SurfaceD3CircuitDistance.lean`: finite surface-code geometry
  reused by the QClifford proof, plus older appendix cross-checks.
- `docs/surface_d3_nz_qclifford_geometric_hoare_certificate.json` with
  `tools/check_geometric_hoare.py` and `tools/qhl_semantic.py`: independent
  certificate and decision procedure for the QClifford Hoare obligations.
- `tools/check_lean_cert_correspondence.py`: mechanical equality check between
  the QClifford Lean-emitted stabilizers/logicals/gadgets/bound and the
  certificate.
- `tools/verify_all.py`: one-command positive verification plus permanent
  negative regression suite. Its build gate includes
  `QStab.QClifford.Knill`, `Shor`, `Flag`, `FlagGeneral`, the calculus, and
  the NZ/Knill PCC modules, so scheme regressions cannot hide behind a narrow
  build. It also compiles the Shor PCC skeleton and checks that the local
  Shor pair-cancellation tooth is axiom-clean.

## Model Scope

The circuit model is the concrete 9-data-qubit rotated surface-d3 code with one
ancilla qubit and the eight-gadget NZ stabilizer extraction schedule.  Faults
are independent single-location single-qubit Pauli injections at the concrete
`FInstr.errLoc` sites.  QClifford's `F_ErrLoc` rule and `fcevalW` semantics
charge exactly one fault for each injected non-identity branch.

The direct QClifford lower-bound theorem is detection-free:

```lean
distPost σ := σ.lambda <= 2 -> not (logicalFailure σ.es)
```

The exported PCC policy is the post-selected detected-syndrome statement:
`failure spec es := logicalFailure spec es /\ allFlagsZero spec es`.
`undetected spec es` means every stabilizer syndrome bit is zero, where
`syndromeBit spec es i` is the XOR of the raw detector slots in
`spec.stabilizerReadout i`. XOR is only within one stabilizer's readout list;
the `CodeSpec` field `readout_disjoint` requires distinct stabilizers to use
disjoint raw slots. `allFlagsZero` is `undetected` plus any separate
post-selection flags marked by `postselectFlag`.

For NZ surface-d3, each stabilizer readout is a singleton slot. For Knill
surface-d3, each stabilizer readout is the list of raw transversal measurement
slots belonging to that stabilizer. In both cases the reused ancilla identity
is not the detector identity; readout is time-resolved via
`ErrorState.detectors`. Regression theorems pin both bug classes:
`surfaceTwoDetector_not_undetected` rejects cross-stabilizer XOR collapse,
while `combinerPairFlip_syndrome_zero` and
`combinerSingleFlip_syndrome_one` pin the within-stabilizer XOR combiner.

## PCC Trust Contract

The trusted PCC kernel fixes the policy:

```lean
Safe C spec :=
  WellFormed C spec /\
  (readout lists for distinct stabilizers are disjoint) /\
  (forall i E, gadgetMeasFlip C spec i E = parity spec (spec.stabilizer i) E) /\
  ToleratesFaultsΛ C (failure spec) (spec.d - 1) /\
  exists es, fcevalW spec.d C (ErrorState.clean nq) es /\ failure spec es
```

A compiler may supply a numeric `barrier`, a reachability script, and proofs of
the generated fields of `DistanceCertificate`. It cannot change the statement
of `Safe`, the QClifford semantics, or the Hoare rules. The lower-bound part of
`certificate_sound` is proved by building an `FDeriv` and applying
`fhoare_sound` plus `toleratesFaultsΛ_of_hoare`; it does not use
`barrier_tolerates` as the proof of record.

The lazy verifier contract is deliberately small: the verifier kernel-checks the
submitted `DistanceCertificate` term and applies `certificate_sound`. It performs
no code-specific proof search and no enumeration itself; all heavy facts live in
certificate fields supplied by the producer and checked by Lean.

The VCGen layer makes that contract explicit and reusable. Given a concrete
QClifford program AST, a syntactic stabilizer-code spec, a syntactic
extraction/readout spec, a barrier annotation, and a mode, the checker first
interprets `VCInputSyntax.toVCInput`; then the pure generator `vcgen input`
computes a proof-free syntactic artifact. The output syntax is:

- `VCSlot`, a finite syntax of named obligations such as `programEq`, `syn`,
  `step`, `acceptedBound`, `dist`, and `reach`;
- `FHoareSkeleton`, a syntax tree with the QClifford rule names
  `F_Nil`, `F_Gate`, `F_ErrLoc`, `F_App`, and `F_Conseq`;
- `VCFormulaReport`, the shared QHL formulas for failure, all-flags-zero, and
  circuit-distance views.

Only after generation does the checker use `VCSlot.denote` to interpret a
syntactic slot as a Lean proposition. The producer then submits a discharge
object whose field types literally reference `(vcgen input).denoteSlot ...`;
`vcgen_sound` is the only generic checker step. This is the PCC shape: the
compiler controls the annotation and proofs, but not the assertion language,
the generated statement shape, the QClifford semantics, or the Hoare calculus.

For post-selected schemes with detected hooks, the analogous lazy path is
`DistanceCertificate'` plus `certificate_sound'`.  The trusted kernel still
does not search for hook groupings; it checks the submitted
`CancellationBenign` proof and combines it with `NoUndetectedHook` and the
fixed `Safe` policy.  Shor is not yet a closed PCC client in this tree: the
local four-body Shor algebra is present in `QStab/QClifford/Shor.lean`, but the
remaining producer-side obligation is the run-level theorem that every
accepted detector-cancelling dangerous-hook group in the real surface-d3 Shor
circuit multiplies to a benign stabilizer residual. The proposition is named
`QStab.QClifford.PCC.SurfaceD3Shor.surfaceAcceptedBarrierBound`.  The current
lemma ladder reduces this final obligation to the named producer propositions
`fcevalW_linear` and `accepted_contribution_partition_bound`; the latter is
where `detected_group_le` must be proved and assembled with the benign-list
bound.

`verify_all.py` checks that `certificate_sound`, `certificate_sound'`,
`vcgen_sound`, `surfaceD3_safe`, `surfaceD3_knill_safe`, and the closed Shor ladder rungs
build with only standard axioms.  It also axiom-checks the five
bridge/faithfulness theorems that make the shared assertion language
load-bearing: `VCInput.formulaReport_faithful`,
`vcgen_safe_in_assertion_language`, `frontierSkeleton_sound`,
`hoareSkeleton_sound`, and `hoareSkeleton_sound'`.  It further checks that all
nine expected `#print axioms` entries exist in VCGen and that none introduce
nonstandard axioms.  It also checks that a trivial `barrier := fun _ => 0`
certificate and a non-injective flag-slot mapping are rejected by the generated
VCs; the spec also requires `flagSlot i = i.val`, so shifted or permuted flag
mappings are not valid CodeSpecs. It compiles the two-detector and XOR-combiner
regression theorems and checks the NZ/Knill compile-calculus equivalence
theorems.

## Regression Coverage

`tools/verify_all.py` checks that the real artifacts pass, then rejects copied
tampered certificates for:

- bad CNOT order,
- dropped `f<=2` distance clause,
- `XRowsLe := TRUE`,
- bogus `A007` bound `0`,
- consistent over-claim `D=4`,
- consistent under-claim `D=2`,
- certificate `s0` support drift,
- certificate gadget-order drift,
- certificate `LX` support drift,
- certificate distance-bound drift,
- a trivial PCC barrier certificate,
- a wrong PCC flag-slot mapping,
- an over-flagged reachability witness,
- a two-fired-detector state that must not satisfy `undetected`,
- an XOR-combiner pair flip/single flip sanity check.
