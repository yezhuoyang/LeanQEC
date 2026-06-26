# Surface-d3 NZ QClifford Lean Obligation Map

This note maps the Python checker contract for
`surface_d3_nz_qclifford_geometric_hoare_certificate.json` to the authoritative
QClifford Lean development in `QStab/QClifford/SurfaceD3Distance.lean`.

The older `QStab/Paper/SurfaceD3CircuitDistance.lean` file is now an appendix
for the finite surface-code geometry and legacy cross-checks.  The circuit,
fault semantics, Hoare derivation, fault-tolerance theorem, and tightness
witness are QClifford objects.

## Theorem Shape

The main QClifford theorem is:

```lean
surfaceD3_tolerates_two_faults :
  ToleratesFaultsΛ C_NZ_D3 logicalFailure 2
```

where `C_NZ_D3 : FCircuit 10` is the concrete 9-data-plus-ancilla NZ circuit,
and `logicalFailure es := LogicalAny (dataPart es)`.  This is obtained through
the existing QClifford Hoare stack:

```lean
surfaceD3Deriv : FDeriv cleanPre C_NZ_D3 distPost
surfaceD3_hoare : FHoare cleanPre C_NZ_D3 distPost :=
  fhoare_sound surfaceD3Deriv
surfaceD3_tolerates_two_faults :=
  toleratesFaultsΛ_of_hoare C_NZ_D3 logicalFailure 2 surfaceD3_hoare
```

The postcondition is detection-free:

```lean
distPost σ := σ.lambda <= 2 -> not (logicalFailure σ.es)
```

The certificate's `ZeroDet(det[])` hypothesis is therefore sound but vestigial
for this lower bound.  Measurement flips are still part of QClifford's
`ErrorState`; they are simply unused by the lower-bound theorem.

Tightness is also kernel-checked over the same semantics:

```lean
surfaceD3_reachable_three_fault_logical :
  exists es, fcevalW 3 C_NZ_D3 (ErrorState.clean 10) es /\ logicalFailure es

surfaceD3_distance_exact_qclifford :
  ToleratesFaultsΛ C_NZ_D3 logicalFailure 2 /\
    exists es, fcevalW 3 C_NZ_D3 (ErrorState.clean 10) es /\ logicalFailure es
```

## QClifford Hoare Rule Mapping

The derivation object is the existing audited QClifford calculus:

```lean
FDeriv : AssertionF nq -> FCircuit nq -> AssertionF nq -> Type
```

Constructor correspondence:

- `FDeriv.F_Nil` maps to empty-program skip.
- `FDeriv.F_Gate` maps to certificate rule `H-GateFrontier`.
- `FDeriv.F_ErrLoc` maps to certificate rule `H-LocalFaultFrontier`; its
  injection conjunct increments `σ.lambda` by exactly one.
- `FDeriv.F_App` maps to certificate rule `H-Seq`.
- `FDeriv.F_And` is the existing conjunction structural rule; it is not needed
  by the surface-d3 derivation but remains part of the audited calculus.
- `FDeriv.F_Conseq` maps to certificate rule `H-Conseq`.
- `clean_to_frontier`, used by `F_Conseq`, maps to `E-CleanInit`.
- `frontier_to_distPost`, used by `F_Conseq`, maps to `E-FinalGeo`.

There is no new Hoare calculus in the authoritative file, and no escape
constructor is added to `FDeriv`.

## Python Obligations

`OBL-INIT` maps to:

- `QStab.Paper.SurfaceD3CircuitDistance.OBL_INIT`
- `clean_to_frontier`

This proves that `QCState.clean 10` satisfies the initial frontier invariant.

`OBL-STEP` maps to:

- `QSiteSafe`
- `allSitesSafe_G0` through `allSitesSafe_G7`
- `frontier_errLoc_pre`
- `errLocDeriv`
- `frontierDeriv`
- `QStab.Paper.SurfaceD3CircuitDistance.BI_PAIR_pmul_of_delta_safe`

The QClifford fault rule is applied at each concrete `FInstr.errLoc`.  The
frontier assertion is:

```lean
frontier suffix σ :=
  BI_PAIR (dataPart (propagateCircuit suffix σ.es)) σ.lambda
```

Thus deterministic gates shift the frontier by `F_Gate`, and each err location
uses a local propagated delta through the real QClifford suffix
`propagateCircuit (eraseFaults rest)`.

`OBL-DIST` maps to:

- `QStab.Paper.SurfaceD3CircuitDistance.data_distance_from_BI_PAIR`
- `frontier_to_distPost`

The finite geometry proves that `BI_PAIR` plus `LogicalAny` forces at least
three faults.  `frontier_to_distPost` applies this at the empty suffix.

`FORMULA-AGREEMENT` maps to the reused finite geometry definitions:

- `RowHasX`, `ColHasZ`
- `XRowsLe`, `ZColsLe`
- `BI_PAIR`
- `Centralizer`, `Stab`, `LogicalAny`
- `FORMULA_AGREEMENT_XRowsLe`
- `FORMULA_AGREEMENT_ZColsLe`

The QClifford file does not add primitive row/column/logical syntax.  It only
projects the QClifford `ErrorState 10` to the 9-data-qubit `DataPauli` via
`dataPart`.

## Circuit Correspondence

`tools/check_lean_cert_correspondence.py` runs the QClifford Lean emitter in
`QStab/QClifford/SurfaceD3Distance.lean` and compares the emitted stabilizers,
logicals, gadget kinds/orders, and distance bound with the JSON certificate.

Run the full build, correspondence check, and regression battery with:

```text
python tools/verify_all.py
```
