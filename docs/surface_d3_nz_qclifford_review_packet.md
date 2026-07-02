# Surface d=3 NZ QClifford Proof Review Packet

This packet is for an external reviewer or another AI agent.  It explains the
checked QClifford Hoare proof artifacts for the concrete distance-3 surface-code
NZ syndrome-extraction circuit.

## Files To Review

Primary proof artifacts:

1. `docs/surface_d3_nz_qclifford_geometric_hoare_certificate.json`
   Machine certificate.  This is the source of truth consumed by the checker.

2. `tools/check_geometric_hoare.py`
   Standalone syntactic checker.  It does not call Lean, Lake, native_decide, or
   a branch/fault-set enumerator.

3. `docs/surface_d3_nz_qclifford_geometric_hoare_full.qhl`
   Full instruction-level readable Hoare proof.  It contains one triple per
   concrete instrumented QClifford instruction: `P000` through `P111`.

4. `docs/surface_d3_nz_qclifford_geometric_hoare_detailed.qhl`
   Reviewer-grade expanded proof.  It lists A001-A008 proof details, all 24
   NZ hook shape checks, and all 112 primitive Hoare triples with side-condition
   classifications.

5. `docs/surface_d3_nz_qclifford_geometric_hoare_checked.qhl`
   Compact top-level Hoare derivation with lines `000` through `012`.

6. `docs/surface_d3_nz_qclifford_geometric_hoare_proof.txt`
   Human overview and current checker output.

Run:

```powershell
python tools\check_geometric_hoare.py docs\surface_d3_nz_qclifford_geometric_hoare_certificate.json
```

Expected result:

```text
CHECK PASSED: surface_d3_nz_full_circuit_distance
top_level_rule_nodes: 13
assertion_derivation_nodes: 8
deterministic_gate_count: 44
local_fault_site_count: 68
concrete_instruction_count: 112
concrete_instruction_seq_nodes: 111
expanded_hoare_nodes_no_branching: 227
row_cut_equivalence_checks: 3
col_cut_equivalence_checks: 3
hook_suffix_shape_checks: 24
max_top_level_depth: 5
enumerates_global_fault_sets: 0
enumerates_pauli_space: 0
uses_lean_discharge: 0
qhl_view_checked: 1
full_qhl_primitive_lines_checked: 112
detailed_qhl_primitive_lines_checked: 112
detailed_qhl_hook_checks_checked: 24
```

## Exact Theorem

The checked Hoare triple is:

```text
{{ clean[] }} C_NZ_D3 {{ DIST_CIRC_D3 }}
```

where:

```text
clean[] :=
  data[] = I /\ det[] = 0 /\ faults[] = 0

DIST_CIRC_D3 :=
  ZeroDet(det[]) /\ LogicalAny(data[]) -> 3 <= faults[]

LogicalAny(E) :=
  Centralizer(E) /\ not Stab(E)
```

Glossary:

```text
data[]   := the current concrete Pauli residual on data qubits q0..q8
det[]    := the current concrete measurement-result/syndrome bit vector
faults[] := the number of concrete fault-site events so far
ZeroDet(det[]) := every bit of det[] is zero
```

This is the concrete undetected-logical circuit-distance statement:

If the final measurement-result/syndrome record is zero and the final data
residual is a nontrivial logical Pauli, then at least three concrete QClifford
fault locations occurred.

## Concrete Program

Data qubits are a 3 by 3 grid:

```text
row 0: q0 q1 q2
row 1: q3 q4 q5
row 2: q6 q7 q8

col 0: q0 q3 q6
col 1: q1 q4 q7
col 2: q2 q5 q8
```

The reused syndrome qubit is `q9`.

Stabilizers:

```text
s0 = Z(q0) Z(q1) Z(q3) Z(q4)
s1 = X(q1) X(q2) X(q4) X(q5)
s2 = X(q3) X(q4) X(q6) X(q7)
s3 = Z(q4) Z(q5) Z(q7) Z(q8)
s4 = X(q0) X(q1)
s5 = Z(q2) Z(q5)
s6 = Z(q3) Z(q6)
s7 = X(q7) X(q8)
```

Logical representatives:

```text
LX = X(q0) X(q3) X(q6)
LZ = Z(q0) Z(q1) Z(q2)
```

NZ schedule:

```text
G0 := MeasZStab(s0; q0,q3,q1,q4)
G1 := MeasXStab(s1; q1,q2,q4,q5)
G2 := MeasXStab(s2; q3,q4,q6,q7)
G3 := MeasZStab(s3; q4,q7,q5,q8)
G4 := MeasXStab(s4; q0,q1)
G5 := MeasZStab(s5; q2,q5)
G6 := MeasZStab(s6; q3,q6)
G7 := MeasXStab(s7; q7,q8)

C_NZ_D3 := G0;G1;G2;G3;G4;G5;G6;G7
```

Concrete gadget expansion:

```text
MeasZStab(s; d0,...,dk) :=
  !q9; Prep0(q9);
  !d0; !q9; CX(d0,q9);
  ...
  !dk; !q9; CX(dk,q9);
  !q9; MeasZ(q9)

MeasXStab(s; d0,...,dk) :=
  !q9; PrepP(q9);
  !q9; !d0; CX(q9,d0);
  ...
  !q9; !dk; CX(q9,dk);
  !q9; H(q9);
  !q9; MeasZ(q9)
```

The full expansion is in
`docs/surface_d3_nz_qclifford_geometric_hoare_full.qhl`.

## Assertion Syntax

Core sorts:

```text
Sort ::= Nat | Bool | Qubit | Pauli | PauliVec | MeasVec
       | StabilizerMask
```

Pauli literals:

```text
Pauli ::= I | X | Y | Z
```

Terms:

```text
Term ::= data[] | det[] | faults[] | I
       | q(i)
       | maskAt(m,i)
       | if b then A else B
       | A*B
       | single(q,P)
       | vecAt(E,q)
       | hasX(vecAt(E,q))
       | hasZ(vecAt(E,q))
       | measAt(det[],s)
       | parity(A,E)
```

Formulas:

```text
Formula ::= TRUE | FALSE
          | P /\ Q
          | P \/ Q
          | P -> Q
          | not P
          | t = u
          | n <= m
          | exists x. P
          | forall x. P
```

Every named object below is a derived macro over the kernel syntax.  In
particular, stabilizers, logicals, row/column predicates, `Centralizer`, `Stab`,
`LogicalAny`, `ZeroDet`, `BI_X`, and `BI_Z` are not primitive formula or term
constructors.

Definitions:

```text
q0 := q(0)
q1 := q(1)
q2 := q(2)
q3 := q(3)
q4 := q(4)
q5 := q(5)
q6 := q(6)
q7 := q(7)
q8 := q(8)

s0 := single(q0,Z)*single(q1,Z)*single(q3,Z)*single(q4,Z)
s1 := single(q1,X)*single(q2,X)*single(q4,X)*single(q5,X)
s2 := single(q3,X)*single(q4,X)*single(q6,X)*single(q7,X)
s3 := single(q4,Z)*single(q5,Z)*single(q7,Z)*single(q8,Z)
s4 := single(q0,X)*single(q1,X)
s5 := single(q2,Z)*single(q5,Z)
s6 := single(q3,Z)*single(q6,Z)
s7 := single(q7,X)*single(q8,X)

stabAt(0) := s0
stabAt(1) := s1
stabAt(2) := s2
stabAt(3) := s3
stabAt(4) := s4
stabAt(5) := s5
stabAt(6) := s6
stabAt(7) := s7

ProdStab(m) :=
  (if maskAt(m,0) then s0 else I)*
  (if maskAt(m,1) then s1 else I)*
  (if maskAt(m,2) then s2 else I)*
  (if maskAt(m,3) then s3 else I)*
  (if maskAt(m,4) then s4 else I)*
  (if maskAt(m,5) then s5 else I)*
  (if maskAt(m,6) then s6 else I)*
  (if maskAt(m,7) then s7 else I)

LX := single(q0,X)*single(q3,X)*single(q6,X)
LZ := single(q0,Z)*single(q1,Z)*single(q2,Z)
R0 := single(q0,Z)*single(q1,Z)*single(q2,Z)
R1 := single(q3,Z)*single(q4,Z)*single(q5,Z)
R2 := single(q6,Z)*single(q7,Z)*single(q8,Z)
C0 := single(q0,X)*single(q3,X)*single(q6,X)
C1 := single(q1,X)*single(q4,X)*single(q7,X)
C2 := single(q2,X)*single(q5,X)*single(q8,X)

Centralizer(E) :=
  forall i in {0..7}. parity(stabAt(i),E)=0

Stab(E) :=
  exists stabilizer mask m. E = ProdStab(m)

LogicalAny(E) :=
  Centralizer(E) /\ not Stab(E)

ZeroDet(det[]) :=
  forall s. measAt(det[],s)=0

row(q,0) := q=q(0) \/ q=q(1) \/ q=q(2)
row(q,1) := q=q(3) \/ q=q(4) \/ q=q(5)
row(q,2) := q=q(6) \/ q=q(7) \/ q=q(8)

col(q,0) := q=q(0) \/ q=q(3) \/ q=q(6)
col(q,1) := q=q(1) \/ q=q(4) \/ q=q(7)
col(q,2) := q=q(2) \/ q=q(5) \/ q=q(8)

RowHasX(E,r) :=
  exists q. row(q,r) /\ hasX(vecAt(E,q))

ColHasZ(E,c) :=
  exists q. col(q,c) /\ hasZ(vecAt(E,q))

XRowsAll(E) :=
  RowHasX(E,0) /\ RowHasX(E,1) /\ RowHasX(E,2)

ZColsAll(E) :=
  ColHasZ(E,0) /\ ColHasZ(E,1) /\ ColHasZ(E,2)

XRowsLe(E,f) :=
  (f=0 -> not RowHasX(E,0) /\ not RowHasX(E,1) /\ not RowHasX(E,2)) /\
  (f<=1 -> not ((RowHasX(E,0)/\RowHasX(E,1)) \/
                    (RowHasX(E,0)/\RowHasX(E,2)) \/
                    (RowHasX(E,1)/\RowHasX(E,2)))) /\
  (f<=2 -> not XRowsAll(E))

ZColsLe(E,f) :=
  (f=0 -> not ColHasZ(E,0) /\ not ColHasZ(E,1) /\ not ColHasZ(E,2)) /\
  (f<=1 -> not ((ColHasZ(E,0)/\ColHasZ(E,1)) \/
                    (ColHasZ(E,0)/\ColHasZ(E,2)) \/
                    (ColHasZ(E,1)/\ColHasZ(E,2)))) /\
  (f<=2 -> not ZColsAll(E))

BI_X := exists m. XRowsLe(ProdStab(m)*data[], faults[])
BI_Z := exists m. ZColsLe(ProdStab(m)*data[], faults[])
BI_PAIR := BI_X /\ BI_Z

FULL_INV := BI_PAIR
```

Important point for reviewers: `LogicalAny(E)` is not the old one-direction
parity predicate.  It is exactly `Centralizer(E) /\ not Stab(E)`.

## Command Syntax

```text
Command ::= skip
          | !q
          | Prep0(q)
          | PrepP(q)
          | H(q)
          | CX(q,r)
          | MeasZ(q)
          | C;D
```

Meaning of `!q`:

`!q` is a concrete fault site at physical qubit `q`.  The proof does not print
the three Pauli branches `X/Y/Z`.  Instead, the local QClifford Hoare rule
`H-LocalFaultFrontier` advances an explicit boundary-frontier assertion
`BND[G,k]` to `BND[G,k+1]` using the geometric local-fault lemmas `L001`
through `L004`.  This is the deliberate replacement for the old single-branch
table checker.

Important granularity point:

Interior primitive lines do not claim `{{ FULL_INV }} instr {{ FULL_INV }}`.
They use frontier assertions:

```text
BND[G,k] := BI_PAIR(dataOf(PropDet(Suffix[G,k], phys[])), faults[])
```

`phys[]` is the current concrete Pauli residual over `q0..q9`; `data[]` is
`dataOf(phys[])`.  `Suffix[G,k]` is the remaining deterministic suffix of
gadget `G` after local point `k`, with later `!q` markers erased.  Thus a
partial hook may temporarily violate raw `BI_PAIR(data[],faults[])`; the proof
only requires that the completed deterministic suffix restores the boundary
barrier.

## Assertion Lemmas

The checker verifies the algebraic side conditions for these assertion lemmas.

```text
A001 G-RowCuts:
  R0=LZ, R1=s0*s5*R0, R2=s3*s6*R1.

A002 G-ColCuts:
  C0=LX, C1=s4*s2*C0, C2=s1*s7*C1.

A003 G-HomologyCover:
  Centralizer(E) /\ not Stab(E)
    -> parity(LZ,E)=1 \/ parity(LX,E)=1.

A004 G-RowSpread(A001):
  Centralizer(E) /\ parity(LZ,E)=1
    -> forall m. XRowsAll(ProdStab(m)*E).

A005 G-ColSpread(A002):
  Centralizer(E) /\ parity(LX,E)=1
    -> forall m. ZColsAll(ProdStab(m)*E).

A006 G-LogicalAnyToBarrierZero(A003,A004,A005):
  LogicalAny(E)
    -> (forall m. XRowsAll(ProdStab(m)*E)) \/
       (forall m. ZColsAll(ProdStab(m)*E)).

A007 G-DataDistance(A006):
  BI_PAIR -> (LogicalAny(data[]) -> 3 <= faults[]).

A008 G-FinalCircuitDistance(A007):
  FULL_INV -> DIST_CIRC_D3.
```

The checker verifies:

1. Row and column cut equivalences by symbolic Pauli multiplication.
2. Stabilizer rank is 8.
3. `LX` and `LZ` commute with stabilizers.
4. `LX` and `LZ` anticommute with each other.
5. Stabilizers plus `LX,LZ` span the centralizer quotient.

## Local Geometric Lemmas

These are the local QClifford fault rules consumed by every `!q` triple.

```text
L001 G-DataFaultLocal:
  A single data-qubit Pauli fault satisfies the XRowsLe/ZColsLe one-fault
  extension formulas and increments faults[] by exactly one.

L002 G-NoDataFaultLocal:
  A prep, terminal ancilla, or measurement-result fault site with no data
  residual increments faults[] and preserves BI_PAIR.

L003 G-AncillaFaultLocal:
  An ancilla fault propagates through the concrete CNOT suffix to an NZ hook
  mechanism in the current gadget.

L004 G-NZHookBound:
  Every NZ suffix hook has dangerous spread <= 1 modulo the measured gadget
  stabilizer.
```

The checker verifies 24 concrete suffix-hook shapes, one for each nonempty
data suffix inside the eight gadgets.

## Hoare Logic Rules

These are the allowed proof rules in the certificate.

```text
H-LocalFaultFrontier:
  If the current !q fault is classified by L001, L002, or L003 and any
  resulting hook satisfies L004, then:

    {{ BND[G,k] }} !q {{ BND[G,k+1] }}

H-GateFrontier:
  For a concrete deterministic QClifford primitive U at local point k,
  QClifford Pauli propagation shifts U from the deterministic suffix into the
  current state:

    {{ BND[G,k] }} U {{ BND[G,k+1] }}

H-FrontierDef:
  BND[G,k] is a derived assertion:

    BND[G,k] := BI_PAIR(dataOf(PropDet(Suffix[G,k], phys[])), faults[])

  At gadget boundaries, BND[G,0] and BND[G,end] are definitionally FULL_INV.

H-Seq:
  From:

    {{ P }} A {{ Q }}
    {{ Q }} B {{ R }}

  derive:

    {{ P }} A;B {{ R }}

H-Conseq:
  From:

    P -> P'
    {{ P' }} C {{ Q' }}
    Q' -> Q

  derive:

    {{ P }} C {{ Q }}

E-CleanInit:
  clean[] -> FULL_INV.

E-FinalGeo:
  FULL_INV -> DIST_CIRC_D3 using A008.
```

## Proof Tree

Compact proof:

```text
000. {{ clean[] }} E-CleanInit {{ FULL_INV }}
001..008. {{ FULL_INV }} H-GadgetGeo Gi {{ FULL_INV }}
009. {{ FULL_INV }} H-Seq lines 001..008 over C_NZ_D3 {{ FULL_INV }}
010. {{ clean[] }} H-Conseq using 000 and 009 {{ FULL_INV }}
011. {{ FULL_INV }} E-FinalGeo {{ DIST_CIRC_D3 }}
012. {{ clean[] }} H-Conseq using 010 and 011 {{ DIST_CIRC_D3 }}
```

Expanded proof:

```text
P000..P111:
  one primitive Hoare triple per concrete instrumented instruction

S000:
  H-Seq P000..P111 over C_NZ_D3

F000..F002:
  clean initialization, final consequence, theorem close
```

Machine-checked sizes:

```text
top_level_rule_nodes: 13
assertion_derivation_nodes: 8
primitive_hoare_lines: 112
instruction_sequence_nodes: 111
expanded_hoare_nodes_no_branching: 227
```

## What This Proof Deliberately Does Not Use

The checker rejects the old proof style if it appears in the certificate:

```text
H-CheckedTrace
H-ErrTable
Tbl
branch
branches
fault_pairs
choose
forallErrorVecs
native_decide
Lean_discharge
backActionSet
```

There is no enumeration of:

1. all one-fault Pauli branches,
2. all two-fault combinations,
3. the full 9-qubit Pauli space.

## Trust Boundary And Known Status

Current status:

This is machine-checkable by `tools/check_geometric_hoare.py` as a syntactic
QClifford Hoare certificate.  The concrete distance lower bound has also been
ported into Lean's kernel as
`QStab.Paper.SurfaceD3CircuitDistance.surfaceD3_circuit_distance_lower_bound`.
The matching 3-fault reachability witness is
`QStab.Paper.SurfaceD3CircuitDistance.surfaceD3_distance_reachable`, and the
combined exact-distance statement is
`QStab.Paper.SurfaceD3CircuitDistance.surfaceD3_circuit_distance_exact`.

Trusted components in the standalone checker, when considered without the Lean
port:

1. Pauli vector arithmetic over F2.
2. Small F2 rank computation.
3. Symbolic row/column cut multiplication.
4. The parser/checker for the JSON derivation and `.qhl` views.
5. The schematic validity of `H-LocalFaultFrontier`, `H-GateFrontier`,
   `H-FrontierDef`, `H-Seq`,
   `H-Conseq`, `E-CleanInit`, and `E-FinalGeo`.

Important review target for the remaining design work:

The strongest place to scrutinize is not branch enumeration.  It is how the
frontier schematic rules `H-LocalFaultFrontier`, `H-GateFrontier`, and
`H-FrontierDef` should be packaged as reusable QClifford Hoare rules, and how
`L001` through `L004` should be exposed to the future QStab-to-QClifford proof
compiler.

## Suggested Review Checklist

1. Re-run the checker and confirm the expected output.
2. Inspect the JSON certificate and verify that `LogicalAny` is
   `Centralizer /\ not Stab`.
3. Inspect `A001` and `A002`; confirm the row/column cut equalities.
4. Inspect `A003`; confirm the centralizer quotient basis argument is valid
   for the stated surface-d3 stabilizers.
5. Inspect `L004`; confirm every NZ suffix hook has dangerous spread <= 1.
6. Inspect `docs/surface_d3_nz_qclifford_geometric_hoare_full.qhl`; confirm it
   contains exactly `P000` through `P111` and that `S000/F000/F001/F002` close
   the theorem.
7. Confirm no banned old-checker vocabulary is used as a proof rule.
8. Decide whether the current trusted Hoare rules are acceptable as the
   QClifford proof kernel, or whether one of them should be decomposed further
   before the Lean port.
