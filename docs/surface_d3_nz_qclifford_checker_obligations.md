# Surface-d3 NZ QClifford circuit-distance — proof obligations & prover rules

This document specifies what the **consolidated** checker
(`tools/check_geometric_hoare.py` + `tools/qhl_semantic.py`) now verifies, and
the strict rules a prover (human or agent) must follow so the certificate is
accepted **only when the distance theorem is actually true**.

Run:

```
python tools/check_geometric_hoare.py
```

`CHECK PASSED` now means all obligations below are discharged; `CHECK FAILED`
prints the first failing obligation.

---

## 0. Theorem and model scope

```
{{ clean[] }} C_NZ_D3 {{ DIST_CIRC_D3 }}
DIST_CIRC_D3 := ZeroDet(det[]) /\ LogicalAny(data[]) -> D <= faults[]
```

* **Fault model**: independent single-location single-qubit Pauli faults. Each
  `!q` site fails with one of `{X,Y,Z}` and increments `faults[]` by exactly one.
  Correlated 2-qubit gate faults are *out of scope by assumption* (accepted).
* **`ZeroDet(det[])`** is a sound but *vestigial* hypothesis: the proof
  establishes the stronger `LogicalAny(data[]) -> D <= faults[]` (any logical
  needs `D` faults, detected or not), which implies the stated theorem. The
  invariant does not track `det[]`. This is intentional and correct for a lower
  bound.
* `D` is **not hardcoded**. It is read from `DIST_CIRC_D3` and must equal the
  distance the kernel computes from the circuit (obligation **OBL-DIST**).

## 1. The invariant

```
BI_PAIR := BI_X /\ BI_Z
BI_X    := exists m. XRowsLe(ProdStab(m)*data[], faults[])      (row barrier)
BI_Z    := exists m. ZColsLe(ProdStab(m)*data[], faults[])      (col barrier)
XRowsLe(E,f) <=> (X-row-spread of E) <= f         (capped at 3 rows)
ZColsLe(E,f) <=> (Z-col-spread of E) <= f         (capped at 3 cols)
FULL_INV := BI_PAIR
```

Operationally `BI_PAIR(E,f)` means: modulo the stabilizer group, the data
residual `E` has X-row-spread `<= f` **and** Z-col-spread `<= f`.

The per-instruction frontier assertions remain
`BND[G,k] := BI_PAIR(dataOf(PropDet(Suffix[G,k], phys[])), faults[])`. Gate steps
are definitional (weakest-precondition bookkeeping); the real content is the
fault steps, now discharged by **OBL-STEP**.

---

## 2. Obligations the checker now discharges

| ID | Statement | Verified by | Status |
|----|-----------|-------------|--------|
| **ALG-CUTS** | `R0=LZ`, `R1=s0·s5·R0`, `R2=s3·s6·R1`, and column analogues | `check_cut_equivalences` (symbolic F2 Pauli mult) | machine-verified |
| **ALG-HOM** | 8 stabilizers commute, F2-rank 8; `LX,LZ` commute w/ stabs; `parity(LX,LZ)=1`; stabs+LX+LZ span the dim-10 centralizer | `check_homology_basis` | machine-verified |
| **OBL-INIT** | `clean[]` (data=I, faults=0) ⇒ `BI_PAIR` | `qhl_semantic.check_init` | machine-verified |
| **OBL-STEP** | every `!q` site, every branch `P∈{X,Y,Z}`, propagated through the remaining gadget suffix, yields a data delta with X-row-spread ≤ 1 **and** Z-col-spread ≤ 1 modulo the stabilizer group ⇒ `BI_PAIR` is preserved with `faults+1` | `qhl_semantic.check_step` (implements `PropDet`/`mapCX`/`mapH`, 68 sites × 3 branches = 204 checks) | machine-verified |
| **OBL-DIST** | the computed distance `d* = min over logical reps of max(min-row-spread, min-col-spread)` equals the claimed `D`; and no logical rep satisfies `BI_PAIR` at any `f < D` | `qhl_semantic.check_distance` (768 logical reps × 256 masks) | machine-verified |
| **FORMULA-AGREEMENT** | the certificate's own `XRowsLe`/`ZColsLe`/`BI_PAIR` formula *strings*, evaluated as logic, agree with the operational spreads over identity + all single-qubit Paulis + all 768 logical reps + all 256 stabilizer elements | `qhl_semantic.check_formula_agreement` (parses & evaluates the assertion logic; 8416 + 108 model-checks) | machine-verified |
| **STRUCT** | derivation tree shape, rule names, premise lists, `.qhl` round-trip, and **bound consistency** (A007/A008/goal state the same `D` as `DIST_CIRC_D3`) | `check_assertion_derivations`, `check_hoare_derivation`, `check_*_qhl_view` | machine-verified (structural) |

### Why these are sufficient (soundness sketch)

OBL-INIT + OBL-STEP give `BI_PAIR` as an inductive invariant of `C_NZ_D3`
(subadditivity holds because `ProdStab` is a homomorphism: `ProdStab(a)·ProdStab(b)=ProdStab(a⊕b)`,
so a single mask reduces `E·Δ` to `min-spread(E)+min-spread(Δ) ≤ f+1`). At the
end, `BI_PAIR(data[], faults[])` holds; OBL-DIST shows any `LogicalAny(data[])`
forces `D ≤ faults[]`. FORMULA-AGREEMENT guarantees the prover's stated invariant
is the operational one, so the prover cannot weaken it.

### What the standalone Python checker still trusts

When the certificate is checked only by Python, the Python kernel's own
correctness is the trust base:

1. The propagation equations `mapCX`/`mapH`/`mapPrep`/`mapMeas` and `dataOf`.
2. That gate steps are exactly the WP of the suffix (so they carry no obligation).
3. The spread/distance definitions (`row=q//3`, `col=q%3`) and F2 arithmetic.

These are what `uses_lean_discharge: 0` flags for the standalone checker.  The
surface-d3 NZ lower bound has now been ported into Lean's kernel in
`QStab.Paper.SurfaceD3CircuitDistance.surfaceD3_circuit_distance_lower_bound`;
the exact-distance witness is
`QStab.Paper.SurfaceD3CircuitDistance.surfaceD3_circuit_distance_exact`.
Lean/certificate drift is machine-checked by
`python tools/check_lean_cert_correspondence.py`.

---

## 3. Strict rules the prover MUST follow

A certificate is accepted **iff** all of the following hold.

**R1 — Fixed code.** `derived_terms` for `s0..s7, LX, LZ, R*, C*` must be the
exact canonical strings for the surface-d3 code (pinned by
`check_kernel_assertion_language`). The prover may **not** redefine the code.

**R2 — Fixed invariant shape, verified meaning.** `XRowsLe`, `ZColsLe`, `BI_X`,
`BI_Z`, `BI_PAIR`, `DIST_CIRC_D3` must be present and must **evaluate** to the
operational semantics (FORMULA-AGREEMENT). Gutting a clause (`f<=2 -> ...`),
setting a formula to `TRUE`, or any vacuous rewrite is rejected.

**R3 — Honest schedule.** The gadget `order` lists are the prover's design
freedom, but every fault, on every branch, must propagate to ≤ 1 dangerous
spread (OBL-STEP). A distance-reducing CNOT order is rejected.

**R4 — Tight, consistent bound.** The integer `D` in `DIST_CIRC_D3` must equal
the computed distance `d*` (OBL-DIST: neither over- nor under-claiming), and the
conclusions of A007, A008 and the goal must state the same `D` (STRUCT).

**R5 — No banned shortcuts.** The `prohibits` list (branch/fault-pair
enumeration, `native_decide`, `Lean_discharge`, old boundary-vocabulary, …) must
not appear; `FULL_INV` may appear in a primitive triple only at a gadget
entry/exit.

**R6 — Faithful views.** The `.qhl` views must be the exact renderings of the
certificate (round-trip).

### What gets rejected (regression battery)

These are confirmed `CHECK FAILED`:

* bad CNOT schedule (`G1`/`G3` reorder) — **OBL-STEP**
* dropping the `f<=2` distance clause — **FORMULA-AGREEMENT**
* `XRowsLe := TRUE` (vacuous invariant) — **FORMULA-AGREEMENT**
* `A007` conclusion `0 <= faults[]` — **STRUCT** (bound consistency)
* consistent over-claim `D=4` — **OBL-DIST** (theorem false)
* consistent under-claim `D=2` — **OBL-DIST** (not tight)

The genuine certificate passes with `computed_distance: 3 == claimed_distance: 3`.
