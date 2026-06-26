#!/usr/bin/env python3
"""Checker for the surface-d3 NZ QClifford geometric Hoare certificate.

The checker has two layers.

SYNTACTIC layer (this file):
* the certificate uses only the declared QClifford Hoare/assertion rules;
* the concrete program is the stated eight-gadget NZ schedule;
* row/column cut equivalences hold by symbolic Pauli multiplication;
* LX/LZ form the centralizer quotient basis by small F2 rank checks;
* the derivation tree has the right shape and the data-distance / final-distance
  lemmas state the same bound as the theorem DIST_CIRC_D3;
* the .qhl views are faithful renderings of the certificate.

SEMANTIC layer (``qhl_semantic.py``, invoked from ``check_certificate``):
* OBL-INIT : clean[] => BI_PAIR;
* OBL-STEP : every single-location fault, on every X/Y/Z branch, propagated
  through the remaining gadget suffix, adds <= 1 dangerous spread in each of the
  X-row and Z-column directions modulo the stabilizer group (=> BI_PAIR is
  preserved with faults+1);
* OBL-DIST : the code distance computed from the logical representatives equals
  the bound D claimed by the certificate;
* FORMULA-AGREEMENT : the certificate's own XRowsLe/ZColsLe/BI_PAIR formula
  strings, evaluated as logic, agree with that operational semantics (so a
  vacuous or gutted invariant is rejected).

It still does not enumerate the full 4^9 Pauli space, all global multi-fault
sets, or invoke Lean; the semantic layer enumerates the 1024-element centralizer,
the 256-element stabilizer group, and the 68 single-location fault sites.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import qhl_semantic  # noqa: E402  (semantic kernel; same tools/ directory)


PAULI_TO_BITS = {
    "I": (0, 0),
    "X": (1, 0),
    "Z": (0, 1),
    "Y": (1, 1),
}

BITS_TO_PAULI = {v: k for k, v in PAULI_TO_BITS.items()}


class CheckError(Exception):
    pass


def fail(message: str) -> None:
    raise CheckError(message)


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def qubit_index(q: str) -> int:
    require(q.startswith("q") and q[1:].isdigit(), f"bad qubit name: {q!r}")
    return int(q[1:])


def pauli_from_spec(spec: dict[str, list[str]], qubits: list[str]) -> dict[str, tuple[int, int]]:
    out = {q: (0, 0) for q in qubits}
    for p, qs in spec.items():
        require(p in PAULI_TO_BITS, f"unknown Pauli label {p!r}")
        px, pz = PAULI_TO_BITS[p]
        for q in qs:
            require(q in out, f"unknown data qubit {q!r} in Pauli spec")
            x, z = out[q]
            out[q] = (x ^ px, z ^ pz)
    return out


def pauli_from_kernel_expr(expr: str, qubits: list[str],
                           named: dict[str, dict[str, tuple[int, int]]] | None = None) -> dict[str, tuple[int, int]]:
    """Evaluate the small-kernel Pauli-string fragment used in the certificate.

    Accepted grammar:

      Expr ::= I | Name | single(qN,P) | Expr*Expr

    This intentionally does not understand geometry, rows, columns, or logical
    classes.  It only multiplies explicit single-qubit Pauli strings.
    """
    named = named or {}
    expr = expr.strip()
    if expr == "I":
        return pauli_identity(qubits)
    if expr in named:
        return named[expr]

    out = pauli_identity(qubits)
    for raw_factor in expr.split("*"):
        factor = raw_factor.strip()
        if factor == "I":
            continue
        if factor in named:
            out = pauli_mul(out, named[factor])
            continue
        match = re.fullmatch(r"single\((q[0-8]),([IXYZ])\)", factor)
        require(match is not None, f"unsupported Pauli kernel factor {factor!r} in {expr!r}")
        q, p = match.groups()
        out = pauli_mul(out, pauli_from_spec({p: [q]}, qubits))
    return out


def pauli_mul(a: dict[str, tuple[int, int]], b: dict[str, tuple[int, int]]) -> dict[str, tuple[int, int]]:
    require(a.keys() == b.keys(), "Pauli vectors have different qubit sets")
    return {q: (a[q][0] ^ b[q][0], a[q][1] ^ b[q][1]) for q in a}


def pauli_identity(qubits: list[str]) -> dict[str, tuple[int, int]]:
    return {q: (0, 0) for q in qubits}


def pauli_weight(v: dict[str, tuple[int, int]]) -> int:
    return sum(1 for bits in v.values() if bits != (0, 0))


def pauli_to_bits(v: dict[str, tuple[int, int]], qubits: list[str]) -> list[int]:
    return [v[q][0] for q in qubits] + [v[q][1] for q in qubits]


def symplectic_dot(a: dict[str, tuple[int, int]], b: dict[str, tuple[int, int]]) -> int:
    total = 0
    for q in a:
        ax, az = a[q]
        bx, bz = b[q]
        total ^= (ax & bz) ^ (az & bx)
    return total


def rank_f2(rows: list[list[int]]) -> int:
    rows = [row[:] for row in rows if any(row)]
    if not rows:
        return 0
    width = len(rows[0])
    rank = 0
    col = 0
    while rank < len(rows) and col < width:
        pivot = None
        for r in range(rank, len(rows)):
            if rows[r][col]:
                pivot = r
                break
        if pivot is None:
            col += 1
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for r in range(len(rows)):
            if r != rank and rows[r][col]:
                rows[r] = [x ^ y for x, y in zip(rows[r], rows[rank])]
        rank += 1
        col += 1
    return rank


def row_col_maps(grid: dict[str, list[list[str]]]) -> tuple[dict[str, int], dict[str, int]]:
    row_of: dict[str, int] = {}
    col_of: dict[str, int] = {}
    for r, row in enumerate(grid["rows"]):
        for q in row:
            require(q not in row_of, f"qubit {q} appears in two rows")
            row_of[q] = r
    for c, col in enumerate(grid["cols"]):
        for q in col:
            require(q not in col_of, f"qubit {q} appears in two columns")
            col_of[q] = c
    require(row_of.keys() == col_of.keys(), "row/column qubit sets differ")
    return row_of, col_of


def spread_row_x(v: dict[str, tuple[int, int]], row_of: dict[str, int]) -> int:
    return len({row_of[q] for q, (x, _z) in v.items() if x})


def spread_col_z(v: dict[str, tuple[int, int]], col_of: dict[str, int]) -> int:
    return len({col_of[q] for q, (_x, z) in v.items() if z})


def support_rows_x(v: dict[str, tuple[int, int]], row_of: dict[str, int]) -> list[int]:
    return sorted({row_of[q] for q, (x, _z) in v.items() if x})


def support_cols_z(v: dict[str, tuple[int, int]], col_of: dict[str, int]) -> list[int]:
    return sorted({col_of[q] for q, (_x, z) in v.items() if z})


def pauli_vec_expr(v: dict[str, tuple[int, int]]) -> str:
    parts: list[str] = []
    for q in sorted(v, key=qubit_index):
        bits = v[q]
        if bits != (0, 0):
            parts.append(f"single({q},{BITS_TO_PAULI[bits]})")
    return "*".join(parts) if parts else "I"


def collect_forbidden_strings(obj: Any, forbidden: set[str], path: str = "$") -> list[str]:
    """Scan proof/rule payloads for prohibited old checker vocabulary.

    The certificate's own `prohibits` list is skipped so that naming banned
    words there does not make the certificate reject itself.
    """
    hits: list[str] = []
    if path == "$.prohibits":
        return hits
    if isinstance(obj, dict):
        for key, value in obj.items():
            hits.extend(collect_forbidden_strings(value, forbidden, f"{path}.{key}"))
    elif isinstance(obj, list):
        for i, value in enumerate(obj):
            hits.extend(collect_forbidden_strings(value, forbidden, f"{path}[{i}]"))
    elif isinstance(obj, str):
        for word in forbidden:
            if word in obj:
                hits.append(f"{path}: contains prohibited token {word!r}")
    return hits


def build_named_paulis(cert: dict[str, Any]) -> dict[str, dict[str, tuple[int, int]]]:
    program = cert["program"]
    qubits = program["data_qubits"]
    derived = cert["assertion_syntax"].get("derived_terms", {})
    named: dict[str, dict[str, tuple[int, int]]] = {}
    for name in [f"s{i}" for i in range(8)] + ["LX", "LZ", "R0", "R1", "R2", "C0", "C1", "C2"]:
        require(name in derived, f"missing derived Pauli string {name}")
        named[name] = pauli_from_kernel_expr(derived[name], qubits, named)

    return named


def check_cut_equivalences(cert: dict[str, Any], named: dict[str, dict[str, tuple[int, int]]]) -> tuple[int, int]:
    qubits = cert["program"]["data_qubits"]
    row_checks = 0
    col_checks = 0
    for kind in ["rows", "cols"]:
        for cut in cert["geometric_cuts"][kind]:
            prod = pauli_identity(qubits)
            for factor in cut["equiv_product"]:
                require(factor in named, f"unknown cut-equivalence factor {factor!r}")
                prod = pauli_mul(prod, named[factor])
            require(prod == named[cut["id"]], f"cut equivalence failed for {cut['id']}")
            if kind == "rows":
                row_checks += 1
            else:
                col_checks += 1
    return row_checks, col_checks


def check_homology_basis(cert: dict[str, Any], named: dict[str, dict[str, tuple[int, int]]]) -> None:
    qubits = cert["program"]["data_qubits"]
    stabs = [named[f"s{i}"] for i in range(8)]
    lx = named["LX"]
    lz = named["LZ"]

    for i, a in enumerate(stabs):
        for j, b in enumerate(stabs):
            require(symplectic_dot(a, b) == 0, f"stabilizers s{i}, s{j} anticommute")
    for i, s in enumerate(stabs):
        require(symplectic_dot(s, lx) == 0, f"s{i} anticommutes with LX")
        require(symplectic_dot(s, lz) == 0, f"s{i} anticommutes with LZ")
    require(symplectic_dot(lx, lz) == 1, "LX and LZ must anticommute")

    stab_rank = rank_f2([pauli_to_bits(s, qubits) for s in stabs])
    require(stab_rank == 8, f"expected stabilizer rank 8, got {stab_rank}")

    span_rank = rank_f2([pauli_to_bits(s, qubits) for s in stabs] + [
        pauli_to_bits(lx, qubits),
        pauli_to_bits(lz, qubits),
    ])
    centralizer_dim = 2 * len(qubits) - stab_rank
    require(centralizer_dim == 10, f"expected centralizer dimension 10, got {centralizer_dim}")
    require(span_rank == centralizer_dim, (
        "stabilizers plus LX/LZ do not span the centralizer quotient "
        f"(rank {span_rank}, centralizer dim {centralizer_dim})"
    ))


def check_program(cert: dict[str, Any], named: dict[str, dict[str, tuple[int, int]]]) -> dict[str, int]:
    program = cert["program"]
    require("stabilizers" not in program, "program.stabilizers metadata is not allowed; use derived_terms")
    require("logicals" not in program, "program.logicals metadata is not allowed; use derived_terms")
    qubits = program["data_qubits"]
    row_of, col_of = row_col_maps(program["grid"])
    require(set(row_of) == set(qubits), "grid does not cover exactly the data qubits")
    require(program["ancilla"] == "q9", "expected reused ancilla q9")

    gadget_ids = [g["id"] for g in program["gadgets"]]
    require(gadget_ids == [f"G{i}" for i in range(8)], "gadgets must be G0..G7 in order")

    gate_count = 0
    fault_sites = 0
    hook_suffix_checks = 0
    for gadget in program["gadgets"]:
        kind = gadget["kind"]
        order = gadget["order"]
        stab_name = gadget["stab"]
        require(stab_name in named, f"unknown stabilizer for gadget {gadget['id']}")
        require(len(order) in (2, 4), f"unexpected gadget arity for {gadget['id']}")
        require(len(set(order)) == len(order), f"duplicate data qubit in {gadget['id']}")
        for q in order:
            require(q in qubits, f"unknown data qubit {q} in {gadget['id']}")

        expected_pauli = "Z" if kind == "MeasZStab" else "X" if kind == "MeasXStab" else None
        require(expected_pauli is not None, f"unknown gadget kind {kind!r}")
        expected = pauli_from_spec({expected_pauli: order}, qubits)
        require(expected == named[stab_name], f"{gadget['id']} order does not match {stab_name}")

        k = len(order)
        if kind == "MeasZStab":
            gate_count += k + 2
            fault_sites += 2 * k + 2
        else:
            gate_count += k + 3
            fault_sites += 2 * k + 3

        full_stab = named[stab_name]
        for start in range(k):
            suffix = order[start:]
            hook = pauli_from_spec({expected_pauli: suffix}, qubits)
            hook_mod_stab = pauli_mul(hook, full_stab)
            if kind == "MeasZStab":
                dangerous = min(spread_col_z(hook, col_of), spread_col_z(hook_mod_stab, col_of))
                harmless = min(spread_row_x(hook, row_of), spread_row_x(hook_mod_stab, row_of))
            else:
                dangerous = min(spread_row_x(hook, row_of), spread_row_x(hook_mod_stab, row_of))
                harmless = min(spread_col_z(hook, col_of), spread_col_z(hook_mod_stab, col_of))
            require(dangerous <= 1, f"{gadget['id']} suffix hook {suffix} has dangerous spread {dangerous}")
            require(harmless == 0, f"{gadget['id']} suffix hook {suffix} has unexpected dual spread {harmless}")
            hook_suffix_checks += 1

    require(gate_count == 44, f"expected 44 deterministic gates, got {gate_count}")
    require(fault_sites == 68, f"expected 68 local fault sites, got {fault_sites}")
    return {
        "gate_count": gate_count,
        "fault_site_count": fault_sites,
        "instruction_count": gate_count + fault_sites,
        "hook_suffix_checks": hook_suffix_checks,
    }


def hook_details(cert: dict[str, Any], named: dict[str, dict[str, tuple[int, int]]]) -> list[dict[str, Any]]:
    program = cert["program"]
    qubits = program["data_qubits"]
    row_of, col_of = row_col_maps(program["grid"])
    out: list[dict[str, Any]] = []
    for gadget in program["gadgets"]:
        kind = gadget["kind"]
        order = gadget["order"]
        expected_pauli = "Z" if kind == "MeasZStab" else "X"
        full_stab = named[gadget["stab"]]
        for start in range(len(order)):
            suffix = order[start:]
            hook = pauli_from_spec({expected_pauli: suffix}, qubits)
            hook_mod_stab = pauli_mul(hook, full_stab)
            if kind == "MeasZStab":
                primary = "Z-column-support"
                support = support_cols_z(hook, col_of)
                support_mod = support_cols_z(hook_mod_stab, col_of)
            else:
                primary = "X-row-support"
                support = support_rows_x(hook, row_of)
                support_mod = support_rows_x(hook_mod_stab, row_of)
            out.append({
                "gadget": gadget["id"],
                "kind": kind,
                "stab": gadget["stab"],
                "start": start,
                "suffix": suffix,
                "hook_pauli": expected_pauli,
                "hook": pauli_vec_expr(hook),
                "hook_mod_stab": pauli_vec_expr(hook_mod_stab),
                "primary": primary,
                "support": support,
                "support_mod": support_mod,
                "dangerous": min(len(support), len(support_mod)),
            })
    return out


def gadget_instructions(gadget: dict[str, Any]) -> list[str]:
    order = gadget["order"]
    kind = gadget["kind"]
    if kind == "MeasZStab":
        out = ["!q9", "Prep0(q9)"]
        for q in order:
            out.extend([f"!{q}", "!q9", f"CX({q},q9)"])
        out.extend(["!q9", "MeasZ(q9)"])
        return out
    if kind == "MeasXStab":
        out = ["!q9", "PrepP(q9)"]
        for q in order:
            out.extend(["!q9", f"!{q}", f"CX(q9,{q})"])
        out.extend(["!q9", "H(q9)", "!q9", "MeasZ(q9)"])
        return out
    fail(f"unknown gadget kind {kind!r}")


def deterministic_suffix(instrs: list[str], start: int) -> list[str]:
    return [instr for instr in instrs[start:] if not instr.startswith("!")]


def frontier_assertion(gadget: dict[str, Any], offset: int) -> str:
    instrs = gadget_instructions(gadget)
    require(0 <= offset <= len(instrs), f"bad frontier offset {offset} for {gadget['id']}")
    if offset == 0 or offset == len(instrs):
        return "FULL_INV"
    return f"BND[{gadget['id']},{offset}]"


def frontier_suffix_text(gadget: dict[str, Any], offset: int) -> str:
    suffix = deterministic_suffix(gadget_instructions(gadget), offset)
    return ";".join(suffix) if suffix else "skip"


def expected_instructions(cert: dict[str, Any]) -> list[tuple[str, str]]:
    out: list[tuple[str, str]] = []
    for gadget in cert["program"]["gadgets"]:
        out.extend((gadget["id"], instr) for instr in gadget_instructions(gadget))
    return out


def check_assertion_derivations(cert: dict[str, Any]) -> None:
    derivs = cert["assertion_derivations"]
    by_id = {d["id"]: d for d in derivs}
    require(len(by_id) == len(derivs), "duplicate assertion derivation id")
    expected_rules = {
        "A001": "G-RowCuts",
        "A002": "G-ColCuts",
        "A003": "G-HomologyCover",
        "A004": "G-RowSpread",
        "A005": "G-ColSpread",
        "A006": "G-LogicalAnyToBarrierZero",
        "A007": "G-DataDistance",
        "A008": "G-FinalCircuitDistance",
    }
    for did, rule in expected_rules.items():
        require(did in by_id, f"missing assertion derivation {did}")
        require(by_id[did]["rule"] == rule, f"{did} must use {rule}")
    for d in derivs:
        for p in d.get("premises", []):
            require(p in by_id, f"{d['id']} has unknown premise {p}")
    require(by_id["A006"].get("premises") == ["A003", "A004", "A005"], "bad LogicalAny barrier premises")
    require(by_id["A008"].get("premises") == ["A007"], "final circuit-distance step must depend only on G-DataDistance")
    require("ZeroDet(det[])" in by_id["A008"].get("conclusion", ""), "final circuit-distance step must expose ZeroDet")
    require("LogicalAny(data[])" in by_id["A008"].get("conclusion", ""), "final circuit-distance step must expose LogicalAny")
    # Bound consistency: the data-distance and final-distance lemmas must state
    # the SAME bound as the theorem DIST_CIRC_D3 (closes the "conclusion never
    # read" gap; the bound itself is verified semantically in qhl_semantic).
    dist_atom = cert["assertion_syntax"]["atoms"]["DIST_CIRC_D3"]
    bound_match = re.search(r"(\d+)\s*<=\s*faults\[\]", dist_atom)
    require(bound_match is not None, "DIST_CIRC_D3 must state an integer faults[] bound")
    bound_str = f"{bound_match.group(1)} <= faults[]"
    require(bound_str in by_id["A007"].get("conclusion", ""),
            f"A007 (G-DataDistance) conclusion must state the theorem bound {bound_str!r}")
    require(bound_str in by_id["A008"].get("conclusion", ""),
            f"A008 (G-FinalCircuitDistance) conclusion must state the theorem bound {bound_str!r}")


def check_kernel_assertion_language(cert: dict[str, Any]) -> None:
    syntax = cert["assertion_syntax"]
    terms = syntax["terms"]
    forbidden_kernel_terms = [
        "RowX(",
        "ColZ(",
        "betaX(",
        "betaZ(",
        "Gamma",
        "ChainInv",
        "Weight(",
        "DataBoundary(",
        "DetectorBoundary(",
        "DetectorVec",
    ]
    for term in terms:
        for token in forbidden_kernel_terms:
            require(token not in term, f"kernel term list illegally contains {token}")
    require("phys[]" in terms, "kernel term list must expose the full QClifford Pauli residual phys[]")
    require("dataOf(E)" in terms, "kernel term list must expose data projection dataOf(E)")
    require("ProdStab(m)" not in terms, "ProdStab must be a derived term, not a kernel term")

    derived_terms = syntax.get("derived_terms", {})
    expected_derived_terms = {
        "q0": "q(0)",
        "q1": "q(1)",
        "q2": "q(2)",
        "q3": "q(3)",
        "q4": "q(4)",
        "q5": "q(5)",
        "q6": "q(6)",
        "q7": "q(7)",
        "q8": "q(8)",
        "s0": "single(q0,Z)*single(q1,Z)*single(q3,Z)*single(q4,Z)",
        "s1": "single(q1,X)*single(q2,X)*single(q4,X)*single(q5,X)",
        "s2": "single(q3,X)*single(q4,X)*single(q6,X)*single(q7,X)",
        "s3": "single(q4,Z)*single(q5,Z)*single(q7,Z)*single(q8,Z)",
        "s4": "single(q0,X)*single(q1,X)",
        "s5": "single(q2,Z)*single(q5,Z)",
        "s6": "single(q3,Z)*single(q6,Z)",
        "s7": "single(q7,X)*single(q8,X)",
        "stabAt(0)": "s0",
        "stabAt(1)": "s1",
        "stabAt(2)": "s2",
        "stabAt(3)": "s3",
        "stabAt(4)": "s4",
        "stabAt(5)": "s5",
        "stabAt(6)": "s6",
        "stabAt(7)": "s7",
        "LX": "single(q0,X)*single(q3,X)*single(q6,X)",
        "LZ": "single(q0,Z)*single(q1,Z)*single(q2,Z)",
        "R0": "single(q0,Z)*single(q1,Z)*single(q2,Z)",
        "R1": "single(q3,Z)*single(q4,Z)*single(q5,Z)",
        "R2": "single(q6,Z)*single(q7,Z)*single(q8,Z)",
        "C0": "single(q0,X)*single(q3,X)*single(q6,X)",
        "C1": "single(q1,X)*single(q4,X)*single(q7,X)",
        "C2": "single(q2,X)*single(q5,X)*single(q8,X)",
    }
    for name, expected in expected_derived_terms.items():
        require(derived_terms.get(name) == expected, f"bad derived term {name}")
    prod = derived_terms.get("ProdStab(m)", "")
    for i in range(8):
        require(f"maskAt(m,{i})" in prod and f"s{i}" in prod, f"ProdStab(m) must mention mask bit and s{i}")
    for forbidden in ["RowX", "ColZ", "betaX", "betaZ", "Geometry", "LogicalClass"]:
        for name, body in derived_terms.items():
            require(forbidden not in name and forbidden not in body, f"derived term {name} contains forbidden shortcut {forbidden}")

    derived = syntax.get("derived_formulas", {})
    expected_formulas = {
        "row(q,0)": "q=q(0) \\/ q=q(1) \\/ q=q(2)",
        "row(q,1)": "q=q(3) \\/ q=q(4) \\/ q=q(5)",
        "row(q,2)": "q=q(6) \\/ q=q(7) \\/ q=q(8)",
        "col(q,0)": "q=q(0) \\/ q=q(3) \\/ q=q(6)",
        "col(q,1)": "q=q(1) \\/ q=q(4) \\/ q=q(7)",
        "col(q,2)": "q=q(2) \\/ q=q(5) \\/ q=q(8)",
        "RowHasX(E,r)": "exists q. row(q,r) /\\ hasX(vecAt(E,q))",
        "ColHasZ(E,c)": "exists q. col(q,c) /\\ hasZ(vecAt(E,q))",
        "XRowsAll(E)": "RowHasX(E,0) /\\ RowHasX(E,1) /\\ RowHasX(E,2)",
        "ZColsAll(E)": "ColHasZ(E,0) /\\ ColHasZ(E,1) /\\ ColHasZ(E,2)",
    }
    for name, expected in expected_formulas.items():
        require(derived.get(name) == expected, f"bad derived formula {name}")
    require("XRowsLe(E,f)" in derived, "missing derived formula XRowsLe(E,f)")
    require("ZColsLe(E,f)" in derived, "missing derived formula ZColsLe(E,f)")

    atoms = syntax["atoms"]
    require(atoms["BI_X"] == "exists m. XRowsLe(ProdStab(m)*data[], faults[])", "BI_X must be expanded through XRowsLe")
    require(atoms["BI_Z"] == "exists m. ZColsLe(ProdStab(m)*data[], faults[])", "BI_Z must be expanded through ZColsLe")
    require(atoms["FULL_INV"] == "BI_PAIR", "FULL_INV must not hide a chain/detector-boundary invariant")
    require("ChainInv" not in atoms, "ChainInv must not be an assertion atom in this proof")
    require(atoms["ZeroDet(det[])"] == "forall s. measAt(det[],s)=0", "ZeroDet must be expanded through measurement bits")
    require(atoms["clean[]"] == "data[] = I /\\ det[] = 0 /\\ faults[] = 0", "clean[] must initialize the measurement record")
    # The theorem SHAPE is fixed, but the distance bound is NOT hardcoded here:
    # it is an integer that the semantic kernel (qhl_semantic.check_distance)
    # must prove equals the computed code distance.
    require(
        re.fullmatch(r"ZeroDet\(det\[\]\) /\\ LogicalAny\(data\[\]\) -> \d+ <= faults\[\]", atoms["DIST_CIRC_D3"]) is not None,
        "DIST_CIRC_D3 must be 'ZeroDet(det[]) /\\ LogicalAny(data[]) -> <N> <= faults[]'",
    )
    require(atoms["Centralizer(E)"] == "forall i in {0..7}. parity(stabAt(i),E)=0", "Centralizer must be expanded through stabAt")
    require(atoms["Stab(E)"] == "exists stabilizer mask m. E = ProdStab(m)", "Stab must be expanded through ProdStab")
    require("Centralizer(E) /\\ not Stab(E)" in atoms["LogicalAny(E)"], "LogicalAny must be Centralizer and not Stab")


def check_hoare_derivation(cert: dict[str, Any]) -> None:
    rules = {r["id"] for r in cert["hoare_rules"]}
    local = {l["id"] for l in cert["local_geometric_lemmas"]}
    assertions = {a["id"] for a in cert["assertion_derivations"]}
    derivs = cert["derivation"]
    by_id = {d["id"]: d for d in derivs}
    require(len(by_id) == len(derivs), "duplicate Hoare derivation id")
    require(cert["root"] == "D012", "root must be D012")

    for d in derivs:
        require(d["rule"] in rules, f"{d['id']} uses undeclared rule {d['rule']}")
        for p in d.get("premises", []):
            require(p in local or p in assertions, f"{d['id']} has unknown premise {p}")
        for c in d.get("children", []):
            require(c in by_id, f"{d['id']} has unknown child {c}")

    require(by_id["D000"]["rule"] == "E-CleanInit", "D000 must initialize clean[]")
    require(by_id["D000"]["pre"] == "clean[]" and by_id["D000"]["post"] == "FULL_INV", "bad D000 endpoints")

    for i in range(1, 9):
        d = by_id[f"D00{i}"]
        require(d["rule"] == "H-GadgetGeo", f"D00{i} must be H-GadgetGeo")
        require(d["pre"] == "FULL_INV" and d["post"] == "FULL_INV", f"D00{i} must preserve FULL_INV")
        require(d["program"] == f"G{i - 1}", f"D00{i} must cover G{i - 1}")
        require(set(d.get("premises", [])) == {"L001", "L002", "L003", "L004"}, f"D00{i} bad local premises")

    require(by_id["D009"]["rule"] == "H-Seq", "D009 must sequence gadgets")
    require(by_id["D009"]["children"] == [f"D00{i}" for i in range(1, 9)], "D009 children must be the eight gadget proofs")
    require(by_id["D009"]["pre"] == "FULL_INV" and by_id["D009"]["post"] == "FULL_INV", "D009 endpoints must be FULL_INV")

    require(by_id["D010"]["rule"] == "H-Conseq", "D010 must apply clean consequence")
    require(by_id["D010"]["children"] == ["D000", "D009"], "D010 must use D000 and D009")
    require(by_id["D010"]["pre"] == "clean[]" and by_id["D010"]["post"] == "FULL_INV", "bad D010 endpoints")

    require(by_id["D011"]["rule"] == "E-FinalGeo", "D011 must be final geometric entailment")
    require(by_id["D011"]["premises"] == ["A008"], "D011 must use G-FinalCircuitDistance")
    require(by_id["D011"]["pre"] == "FULL_INV" and by_id["D011"]["post"] == "DIST_CIRC_D3", "bad D011 endpoints")

    root = by_id["D012"]
    require(root["rule"] == "H-Conseq", "root must be H-Conseq")
    require(root["children"] == ["D010", "D011"], "root must combine circuit invariant and final entailment")
    require(root["pre"] == "clean[]" and root["program"] == "C_NZ_D3", "root has wrong pre/program")
    require(root["post"] == "DIST_CIRC_D3", "root must prove DIST_CIRC_D3")

    goal = cert["goal"]
    require(goal["pre"] == root["pre"], "goal pre does not match root")
    require(goal["program"] == root["program"], "goal program does not match root")
    require(goal["post"] == root["post"], "goal post does not match root")
    require("ZeroDet(det[])" in goal["expanded"], "goal must mention ZeroDet(det[])")
    require("det[]" in goal["expanded"], "goal must mention det[]")
    require("LogicalAny(data[])" in goal["expanded"], "goal must mention LogicalAny(data[])")
    # The goal must state the SAME (un-hardcoded) bound as the DIST_CIRC_D3 atom.
    dist_atom = cert["assertion_syntax"]["atoms"]["DIST_CIRC_D3"]
    bound_match = re.search(r"(\d+)\s*<=\s*faults\[\]", dist_atom)
    require(bound_match is not None, "DIST_CIRC_D3 must state an integer faults[] bound")
    require(f"{bound_match.group(1)} <= faults[]" in goal["expanded"],
            "goal must state the same faults[] bound as DIST_CIRC_D3")


def parse_qhl_blocks(path: Path) -> dict[str, dict[str, str]]:
    text = path.read_text(encoding="utf-8").splitlines()
    blocks: dict[str, dict[str, str]] = {}
    i = 0
    while i < len(text):
        match = re.match(r"^(\d{3})\. \{\{ (.*) \}\}\s*$", text[i])
        if match is None:
            i += 1
            continue
        line_id, pre = match.groups()
        require(i + 2 < len(text), f"truncated qhl block at line {line_id}")
        rule = text[i + 1].strip()
        post_match = re.match(r"^\{\{ (.*) \}\}\s*$", text[i + 2].strip())
        require(post_match is not None, f"missing postcondition for qhl line {line_id}")
        require(line_id not in blocks, f"duplicate qhl line {line_id}")
        blocks[line_id] = {
            "pre": pre,
            "rule": rule,
            "post": post_match.group(1),
        }
        i += 3
    return blocks


def check_qhl_view(path: Path, cert: dict[str, Any]) -> None:
    text = path.read_text(encoding="utf-8")
    for token in ["RowX(", "ColZ(", "betaX(", "betaZ(", "Gamma", "ChainInv", "Weight(", "DataBoundary(", "DetectorBoundary(", "DetectorVec"]:
        require(token not in text, f"{path} illegally contains primitive kernel token {token}")
    blocks = parse_qhl_blocks(path)
    expected = {f"{i:03d}" for i in range(13)}
    require(set(blocks) == expected, f"qhl view must contain exactly lines 000..012, got {sorted(blocks)}")

    derivs = {d["id"]: d for d in cert["derivation"]}
    line_to_deriv = {
        "000": "D000",
        "001": "D001",
        "002": "D002",
        "003": "D003",
        "004": "D004",
        "005": "D005",
        "006": "D006",
        "007": "D007",
        "008": "D008",
        "009": "D009",
        "010": "D010",
        "011": "D011",
        "012": "D012",
    }
    for line, did in line_to_deriv.items():
        block = blocks[line]
        deriv = derivs[did]
        require(block["pre"] == deriv["pre"], f"qhl line {line} pre does not match {did}")
        require(block["post"] == deriv["post"], f"qhl line {line} post does not match {did}")
        require(deriv["rule"] in block["rule"], f"qhl line {line} does not mention rule {deriv['rule']}")
        program = deriv.get("program")
        if program and program not in ("skip", "C_NZ_D3"):
            require(program in block["rule"], f"qhl line {line} does not mention program {program}")


def parse_prefixed_qhl_blocks(path: Path, prefix: str) -> dict[str, dict[str, str]]:
    text = path.read_text(encoding="utf-8").splitlines()
    blocks: dict[str, dict[str, str]] = {}
    i = 0
    pattern = re.compile(rf"^{re.escape(prefix)}(\d{{3}})\. \{{\{{ (.*) \}}\}}\s*$")
    while i < len(text):
        match = pattern.match(text[i])
        if match is None:
            i += 1
            continue
        line_id, pre = match.groups()
        require(i + 2 < len(text), f"truncated full qhl block at {prefix}{line_id}")
        rule = text[i + 1].strip()
        post_match = re.match(r"^\{\{ (.*) \}\}\s*$", text[i + 2].strip())
        require(post_match is not None, f"missing postcondition for full qhl line {prefix}{line_id}")
        require(line_id not in blocks, f"duplicate full qhl line {prefix}{line_id}")
        blocks[line_id] = {
            "pre": pre,
            "rule": rule,
            "post": post_match.group(1),
        }
        i += 3
    return blocks


def check_full_qhl_view(path: Path, cert: dict[str, Any]) -> int:
    text = path.read_text(encoding="utf-8")
    for token in ["RowX(", "ColZ(", "betaX(", "betaZ(", "Gamma", "ChainInv", "Weight(", "DataBoundary(", "DetectorBoundary(", "DetectorVec"]:
        require(token not in text, f"{path} illegally contains primitive kernel token {token}")
    blocks = parse_prefixed_qhl_blocks(path, "P")
    rows = flattened_gadget_instructions(cert)
    expected = [(row["gadget"]["id"], row["instr"]) for row in rows]
    require(len(blocks) == len(expected), f"full qhl view must contain {len(expected)} primitive lines")
    for index, row in enumerate(rows):
        gadget = row["gadget"]["id"]
        instr = row["instr"]
        line_id = f"{index:03d}"
        require(line_id in blocks, f"missing full qhl primitive line P{line_id}")
        block = blocks[line_id]
        expected_pre = frontier_assertion(row["gadget"], row["local_index"])
        expected_post = frontier_assertion(row["gadget"], row["local_index"] + 1)
        require(block["pre"] == expected_pre, f"P{line_id} pre must be {expected_pre}, got {block['pre']}")
        require(block["post"] == expected_post, f"P{line_id} post must be {expected_post}, got {block['post']}")
        if expected_pre == "FULL_INV":
            require(row["local_index"] == 0, f"P{line_id} may use FULL_INV as pre only at a gadget entry")
        if expected_post == "FULL_INV":
            require(row["local_index"] + 1 == len(gadget_instructions(row["gadget"])), f"P{line_id} may use FULL_INV as post only at a gadget exit")
        require(gadget in block["rule"], f"P{line_id} must mention gadget {gadget}")
        require(instr in block["rule"], f"P{line_id} must mention instruction {instr}")
        if instr.startswith("!"):
            require("H-LocalFaultFrontier" in block["rule"], f"P{line_id} fault instruction must use H-LocalFaultFrontier")
        else:
            require("H-GateFrontier" in block["rule"], f"P{line_id} gate instruction must use H-GateFrontier")

    seq_blocks = parse_prefixed_qhl_blocks(path, "S")
    require("000" in seq_blocks, "full qhl view must contain S000 sequence fold")
    seq = seq_blocks["000"]
    require(seq["pre"] == "FULL_INV", "S000 must start from FULL_INV")
    require(seq["post"] == "FULL_INV", "S000 must preserve FULL_INV")
    require("H-Seq" in seq["rule"], "S000 must use H-Seq")
    require("P000..P111" in seq["rule"], "S000 must sequence P000..P111")
    require("C_NZ_D3" in seq["rule"], "S000 must sequence over C_NZ_D3")
    return len(expected)


def flattened_gadget_instructions(cert: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    index = 0
    for gadget in cert["program"]["gadgets"]:
        instrs = gadget_instructions(gadget)
        for local_index, instr in enumerate(instrs):
            rows.append({
                "index": index,
                "local_index": local_index,
                "gadget": gadget,
                "instr": instr,
            })
            index += 1
    return rows


def next_gate_in_same_gadget(rows: list[dict[str, Any]], pos: int) -> str | None:
    gadget_id = rows[pos]["gadget"]["id"]
    for row in rows[pos + 1:]:
        if row["gadget"]["id"] != gadget_id:
            return None
        instr = row["instr"]
        if not instr.startswith("!"):
            return instr
    return None


def classify_fault_row(rows: list[dict[str, Any]], pos: int, hook_index_by_key: dict[tuple[str, int], int]) -> str:
    row = rows[pos]
    instr = row["instr"]
    require(instr.startswith("!"), "classify_fault_row expects a fault instruction")
    q = instr[1:]
    gadget = row["gadget"]
    if q != "q9":
        return f"class=data-site; qubit={q}; side=L001; obligation=forall P in {{X,Y,Z}}, residual single({q},P) satisfies XRowsLe/ZColsLe after faults[]+1"

    next_gate = next_gate_in_same_gadget(rows, pos)
    if next_gate and next_gate.startswith("CX("):
        inside = next_gate[3:-1]
        left, right = inside.split(",")
        data_q = right if left == "q9" else left
        if data_q in gadget["order"]:
            start = gadget["order"].index(data_q)
            hidx = hook_index_by_key[(gadget["id"], start)]
            return (
                f"class=ancilla-hook; qubit=q9; next={next_gate}; hook=HCHK{hidx:03d}; "
                "side=L003,L004; obligation=propagate q9 Pauli component through remaining CNOT suffix"
            )
    return "class=no-data; qubit=q9; side=L002; obligation=no data residual, faults[] increments by 1"


def render_detailed_qhl_view(cert: dict[str, Any], named: dict[str, dict[str, tuple[int, int]]], path: Path) -> None:
    hooks = hook_details(cert, named)
    hook_index_by_key = {(h["gadget"], h["start"]): i for i, h in enumerate(hooks)}
    rows = flattened_gadget_instructions(cert)

    lines: list[str] = [
        "# Surface d=3 NZ QClifford fully expanded reviewer proof",
        "#",
        "# This file expands the compact proof obligations behind the generated",
        "# instruction-level Hoare proof.  It is checked for consistency by",
        "# tools/check_geometric_hoare.py.",
        "",
        "THEOREM:",
        "  {{ clean[] }} C_NZ_D3 {{ DIST_CIRC_D3 }}",
        "",
        "KERNEL ONLY:",
        "  Terms are built from phys[], data[], det[], faults[], I, q(i), maskAt(m,i),",
        "  if-then-else, vector product A*B, single(q,P), vecAt(E,q), dataOf(E),",
        "  hasX/hasZ, measAt(det[],s), and parity(A,E).",
        "  All stabilizers, logicals, row/column predicates, and invariants",
        "  below are derived macros over that kernel.",
        "",
        "DERIVED KERNEL MACROS:",
    ]
    derived_terms = cert["assertion_syntax"]["derived_terms"]
    for name in ["q0", "q1", "q2", "q3", "q4", "q5", "q6", "q7", "q8"]:
        lines.append(f"  {name} := {derived_terms[name]}")
    lines.append("")
    for name in ["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7"]:
        lines.append(f"  {name} := {derived_terms[name]}")
    lines.append("")
    for i in range(8):
        name = f"stabAt({i})"
        lines.append(f"  {name} := {derived_terms[name]}")
    lines.append(f"  ProdStab(m) := {derived_terms['ProdStab(m)']}")
    lines.append("")
    for name in ["LX", "LZ", "R0", "R1", "R2", "C0", "C1", "C2"]:
        lines.append(f"  {name} := {derived_terms[name]}")
    lines.extend([
        "",
        "DERIVED FORMULAS:",
    ])
    derived_formulas = cert["assertion_syntax"]["derived_formulas"]
    for name in [
        "row(q,0)", "row(q,1)", "row(q,2)",
        "col(q,0)", "col(q,1)", "col(q,2)",
        "RowHasX(E,r)", "ColHasZ(E,c)",
        "XRowsAll(E)", "ZColsAll(E)",
        "XRowsLe(E,f)", "ZColsLe(E,f)",
    ]:
        lines.append(f"  {name} := {derived_formulas[name]}")
    lines.extend([
        "",
        "DERIVED ASSERTIONS:",
    ])
    for key in ["clean[]", "ZeroDet(det[])", "Centralizer(E)", "Stab(E)", "LogicalAny(E)", "BI_X", "BI_Z", "BI_PAIR", "FULL_INV", "DIST_CIRC_D3"]:
        lines.append(f"  {key} := {cert['assertion_syntax']['atoms'][key]}")
    lines.extend([
        "",
        "ASSERTION DERIVATION DETAILS:",
        "A001. G-RowCuts",
        "  A001.1 R0 = LZ because both expand to single(q0,Z)*single(q1,Z)*single(q2,Z).",
        "  A001.2 s0*s5*R0 = R1 by Pauli cancellation on q0,q1,q2, leaving single(q3,Z)*single(q4,Z)*single(q5,Z).",
        "  A001.3 s3*s6*R1 = R2 by Pauli cancellation on q3,q4,q5, leaving single(q6,Z)*single(q7,Z)*single(q8,Z).",
        "",
        "A002. G-ColCuts",
        "  A002.1 C0 = LX because both expand to single(q0,X)*single(q3,X)*single(q6,X).",
        "  A002.2 s4*s2*C0 = C1 by Pauli cancellation on q0,q3,q6, leaving single(q1,X)*single(q4,X)*single(q7,X).",
        "  A002.3 s1*s7*C1 = C2 by Pauli cancellation on q1,q4,q7, leaving single(q2,X)*single(q5,X)*single(q8,X).",
        "",
        "A003. G-HomologyCover",
        "  A003.1 The checker verifies all stabilizer pairs commute.",
        "  A003.2 The checker verifies LX and LZ commute with every stabilizer.",
        "  A003.3 The checker verifies parity(LX,LZ)=1.",
        "  A003.4 The checker verifies rank(span{s0..s7})=8 over F2.",
        "  A003.5 The checker verifies rank(span{s0..s7,LX,LZ})=10, equal to the centralizer dimension 2*9-8.",
        "  A003.6 Therefore Centralizer(E) /\\ not Stab(E) has nonzero parity with LZ or LX.",
        "",
        "A004. G-RowSpread",
        "  For each row cut Rr, A001 gives Rr = LZ modulo stabilizers.",
        "  If Centralizer(E) and parity(LZ,E)=1, then for every stabilizer mask m, parity(Rr,ProdStab(m)*E)=1.",
        "  Since Rr is a Z-only row string, parity(Rr,ProdStab(m)*E)=1 forces an X or Y component in that row.",
        "  Therefore forall m. XRowsAll(ProdStab(m)*E).",
        "",
        "A005. G-ColSpread",
        "  For each column cut Cc, A002 gives Cc = LX modulo stabilizers.",
        "  If Centralizer(E) and parity(LX,E)=1, then for every stabilizer mask m, parity(Cc,ProdStab(m)*E)=1.",
        "  Since Cc is an X-only column string, parity(Cc,ProdStab(m)*E)=1 forces a Z or Y component in that column.",
        "  Therefore forall m. ZColsAll(ProdStab(m)*E).",
        "",
        "A006. G-LogicalAnyToBarrierZero",
        "  Expand LogicalAny(E) := Centralizer(E) /\\ not Stab(E).",
        "  Apply A003.  The LZ-parity branch uses A004; the LX-parity branch uses A005.",
        "",
        "A007. G-DataDistance",
        "  Expand BI_PAIR := BI_X /\\ BI_Z.",
        "  If LogicalAny(data[]), A006 gives either all X rows for every stabilizer representative or all Z columns for every stabilizer representative.",
        "  BI_X/BI_Z provide an existing stabilizer representative satisfying XRowsLe/ZColsLe at faults[].",
        "  By the f<=2 clauses of XRowsLe/ZColsLe, all three rows/columns are impossible unless 3 <= faults[].",
        "",
        "A008. G-FinalCircuitDistance",
        "  From FULL_INV := BI_PAIR and A007, derive LogicalAny(data[]) -> 3 <= faults[].",
        "  Therefore ZeroDet(det[]) /\\ LogicalAny(data[]) -> 3 <= faults[] by conjunction elimination and implication introduction.",
        "",
        "BOUNDARY-FRONTIER ASSERTIONS:",
        "  phys[] is the current concrete Pauli residual over q0..q9.",
        "  data[] is dataOf(phys[]), the q0..q8 projection.",
        "  dataOf(E) := single(q0,vecAt(E,q0))*single(q1,vecAt(E,q1))*...*single(q8,vecAt(E,q8)).",
        "  PropDet(skip,E) := E.",
        "  PropDet(U;S,E) := PropDet(S, mapU(E)).",
        "  mapCX(c,t,E) := E * (if hasX(vecAt(E,c)) then single(t,X) else I) * (if hasZ(vecAt(E,t)) then single(c,Z) else I).",
        "  mapH(q,E) swaps the X/Z bits of vecAt(E,q) and leaves all other qubits unchanged.",
        "  mapPrep0(q,E), mapPrepP(q,E), and mapMeasZ(q,E) clear the residual component at q.",
        "  BND[G,k] := BI_PAIR(dataOf(PropDet(Suffix[G,k], phys[])), faults[]).",
        "  Suffix[G,k] is the remaining deterministic suffix of gadget G after local point k; all later !q fault markers are erased.",
        "  PropDet is the recursive QClifford Pauli-propagation transformer over that concrete suffix.",
        "  BND[G,0] and BND[G,end] are definitionally FULL_INV at gadget boundaries.",
        "  Interior BND assertions deliberately do not claim raw FULL_INV on the partial data residual.",
        "",
        "CONCRETE FRONTIER DEFINITIONS:",
    ])
    for gadget in cert["program"]["gadgets"]:
        instrs = gadget_instructions(gadget)
        for offset in range(1, len(instrs)):
            lines.append(f"  {frontier_assertion(gadget, offset)} := BI_PAIR(dataOf(PropDet({frontier_suffix_text(gadget, offset)}, phys[])), faults[])")
        lines.append("")
    lines.extend([
        "NZ HOOK SHAPE CHECKS:",
    ])
    for i, h in enumerate(hooks):
        lines.append(
            f"HCHK{i:03d}. gadget={h['gadget']} kind={h['kind']} start={h['start']} "
            f"suffix={','.join(h['suffix'])} hookPauli={h['hook_pauli']} "
            f"hook={h['hook']} hookTimesStab={h['hook_mod_stab']} "
            f"measure={h['primary']} support={h['support']} supportAfterStab={h['support_mod']} "
            f"minSupport={h['dangerous']} <= 1"
        )
    lines.extend([
        "",
        "PRIMITIVE HOARE LINES WITH SIDE CONDITIONS:",
    ])
    for row in rows:
        idx = row["index"]
        instr = row["instr"]
        gadget_id = row["gadget"]["id"]
        pre = frontier_assertion(row["gadget"], row["local_index"])
        post = frontier_assertion(row["gadget"], row["local_index"] + 1)
        if instr.startswith("!"):
            detail = classify_fault_row(rows, idx, hook_index_by_key)
            rule = "H-LocalFaultFrontier"
        else:
            detail = "class=deterministic-gate; side=H-GateFrontier; obligation=concrete Pauli propagation shifts the deterministic suffix frontier"
            rule = "H-GateFrontier"
        lines.extend([
            f"P{idx:03d}. {{{{ {pre} }}}}",
            f"      {rule} {instr} in {gadget_id}",
            f"      DETAIL {detail}",
            f"      {{{{ {post} }}}}",
            "",
        ])
    lines.extend([
        "S000. {{ FULL_INV }}",
        "      H-Seq P000..P111 over C_NZ_D3",
        "      {{ FULL_INV }}",
        "",
        "F000. {{ clean[] }}",
        "      E-CleanInit using clean[] := data[]=I /\\ det[]=0 /\\ faults[]=0 and FULL_INV := BI_PAIR",
        "      {{ FULL_INV }}",
        "",
        "F001. {{ FULL_INV }}",
        "      E-FinalGeo using A008",
        "      {{ DIST_CIRC_D3 }}",
        "",
        "F002. {{ clean[] }}",
        "      H-Conseq using F000,S000,F001",
        "      {{ DIST_CIRC_D3 }}",
    ])
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def check_detailed_qhl_view(path: Path, cert: dict[str, Any], named: dict[str, dict[str, tuple[int, int]]]) -> dict[str, int]:
    text = path.read_text(encoding="utf-8")
    for marker in [
        "DERIVED KERNEL MACROS:",
        "ProdStab(m) :=",
        "DERIVED FORMULAS:",
        "row(q,0) :=",
        "col(q,0) :=",
        "RowHasX(E,r) :=",
        "ColHasZ(E,c) :=",
        "XRowsLe(E,f) :=",
        "ZColsLe(E,f) :=",
        "BOUNDARY-FRONTIER ASSERTIONS:",
        "CONCRETE FRONTIER DEFINITIONS:",
        "phys[] is the current concrete Pauli residual",
        "dataOf(E) :=",
        "PropDet(skip,E) :=",
    ]:
        require(marker in text, f"detailed proof missing derived definition {marker}")
    for marker in ["A001.", "A002.", "A003.", "A004.", "A005.", "A006.", "A007.", "A008."]:
        require(marker in text, f"detailed proof missing {marker}")
    hooks = hook_details(cert, named)
    for i, h in enumerate(hooks):
        token = f"HCHK{i:03d}. gadget={h['gadget']} kind={h['kind']} start={h['start']}"
        require(token in text, f"detailed proof missing hook check {token}")
        require(f"minSupport={h['dangerous']} <= 1" in text, f"detailed proof missing hook support bound HCHK{i:03d}")
    rows = flattened_gadget_instructions(cert)
    for row in rows:
        idx = row["index"]
        expected_pre = frontier_assertion(row["gadget"], row["local_index"])
        expected_post = frontier_assertion(row["gadget"], row["local_index"] + 1)
        start = text.find(f"P{idx:03d}.")
        require(start >= 0, f"detailed proof missing P{idx:03d}")
        block = text[start: start + 500]
        require(f"P{idx:03d}. {{{{ {expected_pre} }}}}" in block, f"P{idx:03d} must use pre {expected_pre}")
        require(f"{{{{ {expected_post} }}}}" in block, f"P{idx:03d} must use post {expected_post}")
        if row["instr"].startswith("!"):
            require("H-LocalFaultFrontier" in block, f"P{idx:03d} fault must use H-LocalFaultFrontier")
            require("DETAIL class=" in block, f"P{idx:03d} missing fault class detail")
        else:
            require("H-GateFrontier" in block, f"P{idx:03d} gate must use H-GateFrontier")
    for token in ["S000.", "F000.", "F001.", "F002."]:
        require(token in text, f"detailed proof missing {token}")
    return {
        "detailed_hook_checks": len(hooks),
        "detailed_primitive_lines": len(rows),
    }


def render_full_qhl_view(cert: dict[str, Any], path: Path) -> None:
    lines: list[str] = [
        "# Surface d=3 NZ QClifford full instruction-level Hoare proof",
        "#",
        "# This file is generated from the checked JSON certificate.  It expands",
        "# the eight H-GadgetGeo nodes into one Hoare triple per concrete",
        "# instrumented QClifford instruction.  It does not enumerate Pauli",
        "# branches, fault pairs, or the full Pauli space.",
        "#",
        "# Exact theorem:",
        "#   {{ clean[] }} C_NZ_D3 {{ DIST_CIRC_D3 }}",
        "# where:",
        "#   DIST_CIRC_D3 := ZeroDet(det[]) /\\ LogicalAny(data[]) -> 3 <= faults[]",
        "#",
        "# The proof is syntactic relative to the rule schemas listed below.  No",
        "# line invokes Lean, native_decide, H-CheckedTrace, H-ErrTable, Tbl,",
        "# backActionSet, branch enumeration, or fault-pair enumeration.",
        "",
        "SYNTAX Sort ::=",
        "  Nat | Bool | Qubit | Pauli | PauliVec | MeasVec | StabilizerMask",
        "",
        "SYNTAX Pauli ::= I | X | Y | Z",
        "",
        "SYNTAX Term ::=",
        "  phys[] | data[] | det[] | faults[] | I |",
        "  q(i) | maskAt(m,i) | if b then A else B | A*B |",
        "  single(q,P) | vecAt(E,q) | dataOf(E) | hasX(vecAt(E,q)) |",
        "  hasZ(vecAt(E,q)) | measAt(det[],s) | parity(A,E)",
        "",
        "SYNTAX Formula ::=",
        "  TRUE | FALSE | P /\\ Q | P \\/ Q | P -> Q | not P |",
        "  t = u | n <= m | exists x. P | forall x. P",
        "",
        "NOTE:",
        "  Every named object below is a derived macro over the kernel syntax.",
        "  In particular, stabilizers, logicals, row/column predicates,",
        "  Centralizer, Stab, LogicalAny, ZeroDet, BI_X, and BI_Z are not",
        "  primitive Formula or Term constructors.",
        "",
        "SYNTAX Command ::=",
        "  skip | !q | Prep0(q) | PrepP(q) | H(q) | CX(q,r) | MeasZ(q) | C;D",
        "",
        "MEANING !q:",
        "  A concrete single-location QClifford fault site at physical qubit q.",
        "  Its Pauli branch semantics is not printed as X/Y/Z branches here;",
        "  H-LocalFaultFrontier advances the boundary-frontier assertion.",
        "",
        "DERIVED q0 := q(0)",
        "DERIVED q1 := q(1)",
        "DERIVED q2 := q(2)",
        "DERIVED q3 := q(3)",
        "DERIVED q4 := q(4)",
        "DERIVED q5 := q(5)",
        "DERIVED q6 := q(6)",
        "DERIVED q7 := q(7)",
        "DERIVED q8 := q(8)",
        "",
        "DERIVED s0 := single(q0,Z)*single(q1,Z)*single(q3,Z)*single(q4,Z)",
        "DERIVED s1 := single(q1,X)*single(q2,X)*single(q4,X)*single(q5,X)",
        "DERIVED s2 := single(q3,X)*single(q4,X)*single(q6,X)*single(q7,X)",
        "DERIVED s3 := single(q4,Z)*single(q5,Z)*single(q7,Z)*single(q8,Z)",
        "DERIVED s4 := single(q0,X)*single(q1,X)",
        "DERIVED s5 := single(q2,Z)*single(q5,Z)",
        "DERIVED s6 := single(q3,Z)*single(q6,Z)",
        "DERIVED s7 := single(q7,X)*single(q8,X)",
        "DERIVED stabAt(0) := s0",
        "DERIVED stabAt(1) := s1",
        "DERIVED stabAt(2) := s2",
        "DERIVED stabAt(3) := s3",
        "DERIVED stabAt(4) := s4",
        "DERIVED stabAt(5) := s5",
        "DERIVED stabAt(6) := s6",
        "DERIVED stabAt(7) := s7",
        "DERIVED ProdStab(m) :=",
        "  (if maskAt(m,0) then s0 else I)*(if maskAt(m,1) then s1 else I)*",
        "  (if maskAt(m,2) then s2 else I)*(if maskAt(m,3) then s3 else I)*",
        "  (if maskAt(m,4) then s4 else I)*(if maskAt(m,5) then s5 else I)*",
        "  (if maskAt(m,6) then s6 else I)*(if maskAt(m,7) then s7 else I)",
        "",
        "DERIVED LX := single(q0,X)*single(q3,X)*single(q6,X)",
        "DERIVED LZ := single(q0,Z)*single(q1,Z)*single(q2,Z)",
        "DERIVED R0 := single(q0,Z)*single(q1,Z)*single(q2,Z)",
        "DERIVED R1 := single(q3,Z)*single(q4,Z)*single(q5,Z)",
        "DERIVED R2 := single(q6,Z)*single(q7,Z)*single(q8,Z)",
        "DERIVED C0 := single(q0,X)*single(q3,X)*single(q6,X)",
        "DERIVED C1 := single(q1,X)*single(q4,X)*single(q7,X)",
        "DERIVED C2 := single(q2,X)*single(q5,X)*single(q8,X)",
        "",
        "DERIVED-ASSERTION clean[] := data[] = I /\\ det[] = 0 /\\ faults[] = 0",
        "DERIVED-ASSERTION ZeroDet(det[]) := forall s. measAt(det[],s)=0",
        "DERIVED-ASSERTION Centralizer(E) := forall i in {0..7}. parity(stabAt(i),E)=0",
        "DERIVED-ASSERTION Stab(E) := exists stabilizer mask m. E = ProdStab(m)",
        "DERIVED-ASSERTION LogicalAny(E) := Centralizer(E) /\\ not Stab(E)",
        "",
        "DERIVED row(q,0) := q=q(0) \\/ q=q(1) \\/ q=q(2)",
        "DERIVED row(q,1) := q=q(3) \\/ q=q(4) \\/ q=q(5)",
        "DERIVED row(q,2) := q=q(6) \\/ q=q(7) \\/ q=q(8)",
        "DERIVED col(q,0) := q=q(0) \\/ q=q(3) \\/ q=q(6)",
        "DERIVED col(q,1) := q=q(1) \\/ q=q(4) \\/ q=q(7)",
        "DERIVED col(q,2) := q=q(2) \\/ q=q(5) \\/ q=q(8)",
        "DERIVED RowHasX(E,r) := exists q. row(q,r) /\\ hasX(vecAt(E,q))",
        "DERIVED ColHasZ(E,c) := exists q. col(q,c) /\\ hasZ(vecAt(E,q))",
        "DERIVED XRowsAll(E) := RowHasX(E,0) /\\ RowHasX(E,1) /\\ RowHasX(E,2)",
        "DERIVED ZColsAll(E) := ColHasZ(E,0) /\\ ColHasZ(E,1) /\\ ColHasZ(E,2)",
        "DERIVED XRowsLe(E,f) :=",
        "  (f=0 -> not RowHasX(E,0) /\\ not RowHasX(E,1) /\\ not RowHasX(E,2)) /\\",
        "  (f<=1 -> not ((RowHasX(E,0)/\\RowHasX(E,1)) \\/",
        "                    (RowHasX(E,0)/\\RowHasX(E,2)) \\/",
        "                    (RowHasX(E,1)/\\RowHasX(E,2)))) /\\",
        "  (f<=2 -> not XRowsAll(E))",
        "DERIVED ZColsLe(E,f) :=",
        "  (f=0 -> not ColHasZ(E,0) /\\ not ColHasZ(E,1) /\\ not ColHasZ(E,2)) /\\",
        "  (f<=1 -> not ((ColHasZ(E,0)/\\ColHasZ(E,1)) \\/",
        "                    (ColHasZ(E,0)/\\ColHasZ(E,2)) \\/",
        "                    (ColHasZ(E,1)/\\ColHasZ(E,2)))) /\\",
        "  (f<=2 -> not ZColsAll(E))",
        "",
        "DERIVED-ASSERTION BI_X := exists m. XRowsLe(ProdStab(m)*data[], faults[])",
        "DERIVED-ASSERTION BI_Z := exists m. ZColsLe(ProdStab(m)*data[], faults[])",
        "DERIVED-ASSERTION BI_PAIR := BI_X /\\ BI_Z",
        "DERIVED-ASSERTION FULL_INV := BI_PAIR",
        "DERIVED-ASSERTION DIST_CIRC_D3 := ZeroDet(det[]) /\\ LogicalAny(data[]) -> 3 <= faults[]",
        "",
        "ASSERTION-LEMMA A001 G-RowCuts:",
        "  R0=LZ, R1=s0*s5*R0, R2=s3*s6*R1.",
        "",
        "ASSERTION-LEMMA A002 G-ColCuts:",
        "  C0=LX, C1=s4*s2*C0, C2=s1*s7*C1.",
        "",
        "ASSERTION-LEMMA A003 G-HomologyCover:",
        "  Centralizer(E) /\\ not Stab(E) -> parity(LZ,E)=1 \\/ parity(LX,E)=1.",
        "",
        "ASSERTION-LEMMA A004 G-RowSpread(A001):",
        "  Centralizer(E) /\\ parity(LZ,E)=1 -> forall m. XRowsAll(ProdStab(m)*E).",
        "",
        "ASSERTION-LEMMA A005 G-ColSpread(A002):",
        "  Centralizer(E) /\\ parity(LX,E)=1 -> forall m. ZColsAll(ProdStab(m)*E).",
        "",
        "ASSERTION-LEMMA A006 G-LogicalAnyToBarrierZero(A003,A004,A005):",
        "  LogicalAny(E) ->",
        "    (forall m. XRowsAll(ProdStab(m)*E)) \\/",
        "    (forall m. ZColsAll(ProdStab(m)*E)).",
        "",
        "ASSERTION-LEMMA A007 G-DataDistance(A006):",
        "  BI_PAIR -> (LogicalAny(data[]) -> 3 <= faults[]).",
        "",
        "ASSERTION-LEMMA A008 G-FinalCircuitDistance(A007):",
        "  FULL_INV -> DIST_CIRC_D3.",
        "",
        "LOCAL-LEMMA L001 G-DataFaultLocal:",
        "  a single data-qubit Pauli fault satisfies the XRowsLe/ZColsLe",
        "  one-fault extension formulas and increments faults[] by exactly one.",
        "",
        "LOCAL-LEMMA L002 G-NoDataFaultLocal:",
        "  a prep, terminal ancilla, or measurement-result fault site with no",
        "  data residual increments faults[] and preserves BI_PAIR.",
        "",
        "LOCAL-LEMMA L003 G-AncillaFaultLocal:",
        "  an ancilla fault propagates through the concrete CNOT suffix to an NZ",
        "  hook mechanism in the current gadget.",
        "",
        "LOCAL-LEMMA L004 G-NZHookBound:",
        "  every NZ suffix hook has dangerous spread <= 1 modulo the measured",
        "  gadget stabilizer.  The checker verifies 24 such suffix-hook shapes.",
        "",
        "FRONTIER TRANSFORMER DEFINITIONS:",
        "  phys[] is the current concrete Pauli residual over q0..q9.",
        "  data[] is dataOf(phys[]), the q0..q8 projection.",
        "  dataOf(E) := single(q0,vecAt(E,q0))*single(q1,vecAt(E,q1))*...*single(q8,vecAt(E,q8)).",
        "  PropDet(skip,E) := E.",
        "  PropDet(U;S,E) := PropDet(S, mapU(E)).",
        "  mapCX(c,t,E) := E * (if hasX(vecAt(E,c)) then single(t,X) else I) *",
        "                    (if hasZ(vecAt(E,t)) then single(c,Z) else I).",
        "  mapH(q,E) swaps the X/Z bits of vecAt(E,q) and leaves all other qubits unchanged.",
        "  mapPrep0(q,E), mapPrepP(q,E), and mapMeasZ(q,E) clear the residual component at q.",
        "",
        "FRONTIER ASSERTIONS:",
        "  BND[G,k] is a derived assertion, not a kernel primitive:",
        "    BND[G,k] := BI_PAIR(dataOf(PropDet(Suffix[G,k], phys[])), faults[])",
        "  Suffix[G,k] is the concrete deterministic suffix of gadget G after",
        "  instrumented local point k, with later !q fault markers erased.",
        "  PropDet is recursively expanded by the QClifford gate propagation",
        "  equations for Prep0, PrepP, H, CX, and MeasZ.",
        "  At gadget boundaries, BND[G,0] and BND[G,end] are definitionally",
        "  FULL_INV.  Interior BND assertions may hold even when raw BI_PAIR",
        "  on the current partial data residual is false.",
        "",
        "RULE H-LocalFaultFrontier:",
        "  If the current !q fault is classified by L001, L002, or L003 and any",
        "  resulting hook satisfies L004, then the concrete local fault advances",
        "  the frontier assertion:",
        "    {{ BND[G,k] }} !q {{ BND[G,k+1] }}.",
        "",
        "RULE H-GateFrontier:",
        "  For a concrete deterministic QClifford primitive U at local point k,",
        "  QClifford Pauli propagation shifts U from the suffix into the current",
        "  state and derives",
        "    {{ BND[G,k] }} U {{ BND[G,k+1] }}.",
        "",
        "RULE H-Seq:",
        "  From {{ P }} A {{ Q }} and {{ Q }} B {{ R }}, derive",
        "    {{ P }} A;B {{ R }}.",
        "",
        "RULE H-Conseq:",
        "  From P -> P', {{ P' }} C {{ Q' }}, and Q' -> Q, derive",
        "    {{ P }} C {{ Q }}.",
        "",
        "RULE E-CleanInit:",
        "  clean[] -> FULL_INV.",
        "",
        "RULE E-FinalGeo:",
        "  FULL_INV -> DIST_CIRC_D3 using A008.",
        "",
        "PROGRAM C_NZ_D3 := G0;G1;G2;G3;G4;G5;G6;G7",
        "",
        "PROGRAM G0 := MeasZStab(s0; q0,q3,q1,q4)",
        "PROGRAM G1 := MeasXStab(s1; q1,q2,q4,q5)",
        "PROGRAM G2 := MeasXStab(s2; q3,q4,q6,q7)",
        "PROGRAM G3 := MeasZStab(s3; q4,q7,q5,q8)",
        "PROGRAM G4 := MeasXStab(s4; q0,q1)",
        "PROGRAM G5 := MeasZStab(s5; q2,q5)",
        "PROGRAM G6 := MeasZStab(s6; q3,q6)",
        "PROGRAM G7 := MeasXStab(s7; q7,q8)",
        "",
    ]
    for gadget in cert["program"]["gadgets"]:
        instrs = gadget_instructions(gadget)
        for offset in range(1, len(instrs)):
            lines.append(f"DERIVED {frontier_assertion(gadget, offset)} := BI_PAIR(dataOf(PropDet({frontier_suffix_text(gadget, offset)}, phys[])), faults[])")
        lines.append("")

    for row in flattened_gadget_instructions(cert):
        index = row["index"]
        gadget = row["gadget"]["id"]
        instr = row["instr"]
        pre = frontier_assertion(row["gadget"], row["local_index"])
        post = frontier_assertion(row["gadget"], row["local_index"] + 1)
        if instr.startswith("!"):
            rule = f"H-LocalFaultFrontier {instr} in {gadget} using L001,L002,L003,L004"
        else:
            rule = f"H-GateFrontier {instr} in {gadget}"
        lines.extend([
            f"P{index:03d}. {{{{ {pre} }}}}",
            f"      {rule}",
            f"      {{{{ {post} }}}}",
            "",
        ])
    lines.extend([
        "S000. {{ FULL_INV }}",
        "      H-Seq P000..P111 over C_NZ_D3",
        "      {{ FULL_INV }}",
        "",
        "F000. {{ clean[] }}",
        "      E-CleanInit",
        "      {{ FULL_INV }}",
        "",
        "F001. {{ FULL_INV }}",
        "      E-FinalGeo using G-FinalCircuitDistance",
        "      {{ DIST_CIRC_D3 }}",
        "",
        "F002. {{ clean[] }}",
        "      H-Conseq using F000,S000,F001",
        "      {{ DIST_CIRC_D3 }}",
        "",
        "CHECKED-SIZE primitive_hoare_lines := 112",
        "CHECKED-SIZE instruction_sequence_nodes := 111",
        "CHECKED-SIZE expanded_hoare_nodes_no_branching := 227",
    ])
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def check_certificate(path: Path) -> dict[str, int]:
    cert = json.loads(path.read_text(encoding="utf-8"))
    require(cert.get("schema") == "qclifford-geometric-hoare-v1", "wrong certificate schema")

    forbidden = set(cert.get("prohibits", []))
    hits = collect_forbidden_strings(cert, forbidden)
    require(not hits, "prohibited old-checker vocabulary:\n" + "\n".join(hits))

    named = build_named_paulis(cert)
    row_cut_checks, col_cut_checks = check_cut_equivalences(cert, named)
    check_homology_basis(cert, named)
    program_counts = check_program(cert, named)
    check_kernel_assertion_language(cert)
    check_assertion_derivations(cert)
    check_hoare_derivation(cert)
    # Semantic kernel: actually compute the code distance, verify per-fault
    # preservation, and tie the prover's invariant strings to the operational
    # semantics.  Raises SemanticError (a subclass-compatible failure) on any
    # vacuous/gutted definition, bad schedule, or wrong distance bound.
    semantic_counts = qhl_semantic.verify(cert, named)

    instruction_count = program_counts["instruction_count"]
    expanded_instruction_tree_nodes = instruction_count + (instruction_count - 1)
    full_expanded_nodes = expanded_instruction_tree_nodes + 4
    counts = {
        "top_level_rule_nodes": len(cert["derivation"]),
        "assertion_derivation_nodes": len(cert["assertion_derivations"]),
        "deterministic_gate_count": program_counts["gate_count"],
        "local_fault_site_count": program_counts["fault_site_count"],
        "concrete_instruction_count": instruction_count,
        "concrete_instruction_seq_nodes": instruction_count - 1,
        "expanded_hoare_nodes_no_branching": full_expanded_nodes,
        "row_cut_equivalence_checks": row_cut_checks,
        "col_cut_equivalence_checks": col_cut_checks,
        "hook_suffix_shape_checks": program_counts["hook_suffix_checks"],
        "max_top_level_depth": 5,
    }
    counts.update(semantic_counts)
    return counts


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "certificate",
        nargs="?",
        default="docs/surface_d3_nz_qclifford_geometric_hoare_certificate.json",
        help="path to the JSON certificate",
    )
    parser.add_argument(
        "--qhl-view",
        default="docs/surface_d3_nz_qclifford_geometric_hoare_checked.qhl",
        help="human-readable qhl proof view to cross-check",
    )
    parser.add_argument(
        "--full-qhl-view",
        default="docs/surface_d3_nz_qclifford_geometric_hoare_full.qhl",
        help="expanded instruction-level qhl proof view to cross-check",
    )
    parser.add_argument(
        "--detailed-qhl-view",
        default="docs/surface_d3_nz_qclifford_geometric_hoare_detailed.qhl",
        help="reviewer-grade detailed qhl proof view to cross-check",
    )
    parser.add_argument(
        "--emit-full-view",
        action="store_true",
        help="regenerate the expanded instruction-level qhl proof view before checking",
    )
    args = parser.parse_args(argv)

    try:
        cert_path = Path(args.certificate)
        counts = check_certificate(cert_path)
        cert = json.loads(cert_path.read_text(encoding="utf-8"))
        named = build_named_paulis(cert)
        if args.emit_full_view:
            render_full_qhl_view(cert, Path(args.full_qhl_view))
            render_detailed_qhl_view(cert, named, Path(args.detailed_qhl_view))
        check_qhl_view(Path(args.qhl_view), cert)
        full_lines = check_full_qhl_view(Path(args.full_qhl_view), cert)
        detailed_counts = check_detailed_qhl_view(Path(args.detailed_qhl_view), cert, named)
    except (CheckError, qhl_semantic.SemanticError) as exc:
        print(f"CHECK FAILED: {exc}", file=sys.stderr)
        return 1

    print("CHECK PASSED: surface_d3_nz_full_circuit_distance")
    for key, value in counts.items():
        print(f"{key}: {value}")
    print("enumerates_global_fault_sets: 0")
    print("enumerates_pauli_space: 0")
    print("uses_lean_discharge: 0")
    print("semantic_distance_verified: 1")
    print(f"semantic_distance_value: {counts['computed_distance']}")
    print("qhl_view_checked: 1")
    print(f"full_qhl_primitive_lines_checked: {full_lines}")
    print(f"detailed_qhl_primitive_lines_checked: {detailed_counts['detailed_primitive_lines']}")
    print(f"detailed_qhl_hook_checks_checked: {detailed_counts['detailed_hook_checks']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
