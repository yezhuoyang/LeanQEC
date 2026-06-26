#!/usr/bin/env python3
"""Check that the Lean surface-d3 proof and JSON certificate describe one object.

The Lean file emits one JSON object derived from the actual Lean stabilizer,
logical, gadget, and distance-bound definitions.  This checker compares that
object against the certificate accepted by ``check_geometric_hoare.py``.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


MARKER = "QCLIFFORD_CERT_CORRESPONDENCE_JSON:"
EXPECTED_STABS = [f"s{i}" for i in range(8)]
EXPECTED_LOGICALS = ["LX", "LZ"]
EXPECTED_GADGETS = [f"G{i}" for i in range(8)]


class CorrespondenceError(Exception):
    pass


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def fail(message: str) -> None:
    raise CorrespondenceError(message)


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def parse_qubit_name(q: str) -> int:
    m = re.fullmatch(r"q(\d+)", q)
    require(m is not None, f"bad qubit name in certificate: {q!r}")
    return int(m.group(1))


def parse_support_term(term_name: str, term: str) -> list[list[Any]]:
    pairs = re.findall(r"single\(q(\d+),(I|X|Y|Z)\)", term)
    require(pairs, f"certificate term {term_name} has no parseable single(q,P) factors")
    return [[int(q), p] for q, p in pairs if p != "I"]


def parse_distance(atom: str) -> int:
    m = re.search(r"(\d+)\s*<=\s*faults\[\]", atom)
    require(m is not None, "certificate DIST_CIRC_D3 has no integer faults[] bound")
    return int(m.group(1))


def run_lean_emitter(lean_file: Path) -> dict[str, Any]:
    root = repo_root()
    proc = subprocess.run(
        ["lake", "env", "lean", str(lean_file)],
        cwd=root,
        text=True,
        capture_output=True,
    )
    combined = proc.stdout.splitlines() + proc.stderr.splitlines()
    if proc.returncode != 0:
        interesting = "\n".join(combined[:20])
        fail(f"Lean emitter failed with exit code {proc.returncode}:\n{interesting}")

    payloads = [line.split(MARKER, 1)[1] for line in combined if MARKER in line]
    require(payloads, f"Lean output did not contain marker {MARKER!r}")
    try:
        return json.loads(payloads[-1])
    except json.JSONDecodeError as exc:
        fail(f"Lean emitted invalid JSON: {exc}")


def normalize_lean(raw: dict[str, Any]) -> dict[str, Any]:
    require(set(raw) == {"stabilizers", "logicals", "gadgets", "distance"},
            f"Lean JSON has unexpected top-level keys: {sorted(raw)}")

    stabs_raw = raw["stabilizers"]
    require(isinstance(stabs_raw, list), "Lean stabilizers field is not a list")
    stabs: dict[str, Any] = {}
    for row in stabs_raw:
        require(isinstance(row, dict), f"Lean stabilizer row is not an object: {row!r}")
        require(set(row) == {"name", "support"}, f"bad Lean stabilizer row keys: {row!r}")
        stabs[row["name"]] = row["support"]
    require(list(stabs) == EXPECTED_STABS, f"Lean stabilizer names are {list(stabs)}, expected {EXPECTED_STABS}")

    logicals = raw["logicals"]
    require(isinstance(logicals, dict), "Lean logicals field is not an object")
    require(sorted(logicals) == EXPECTED_LOGICALS,
            f"Lean logical names are {sorted(logicals)}, expected {EXPECTED_LOGICALS}")

    gadgets_raw = raw["gadgets"]
    require(isinstance(gadgets_raw, list), "Lean gadgets field is not a list")
    gadgets: dict[str, Any] = {}
    for row in gadgets_raw:
        require(isinstance(row, dict), f"Lean gadget row is not an object: {row!r}")
        require(set(row) == {"id", "kind", "order"}, f"bad Lean gadget row keys: {row!r}")
        require(row["kind"] in {"MeasXStab", "MeasZStab"},
                f"Lean gadget {row.get('id')} was not decoded as a stabilizer gadget: {row!r}")
        gadgets[row["id"]] = {"kind": row["kind"], "order": row["order"]}
    require(list(gadgets) == EXPECTED_GADGETS, f"Lean gadget ids are {list(gadgets)}, expected {EXPECTED_GADGETS}")

    distance = raw["distance"]
    require(isinstance(distance, int), f"Lean distance is not an integer: {distance!r}")
    return {"stabilizers": stabs, "logicals": logicals, "gadgets": gadgets, "distance": distance}


def normalize_certificate(path: Path) -> dict[str, Any]:
    cert = json.loads(path.read_text(encoding="utf-8"))
    derived = cert["assertion_syntax"]["derived_terms"]

    stabs = {name: parse_support_term(name, derived[name]) for name in EXPECTED_STABS}
    logicals = {name: parse_support_term(name, derived[name]) for name in EXPECTED_LOGICALS}

    gadgets: dict[str, Any] = {}
    for row in cert["program"]["gadgets"]:
        gid = row["id"]
        gadgets[gid] = {
            "kind": row["kind"],
            "order": [parse_qubit_name(q) for q in row["order"]],
        }
    require(list(gadgets) == EXPECTED_GADGETS,
            f"certificate gadget ids are {list(gadgets)}, expected {EXPECTED_GADGETS}")

    distance = parse_distance(cert["assertion_syntax"]["atoms"]["DIST_CIRC_D3"])
    return {"stabilizers": stabs, "logicals": logicals, "gadgets": gadgets, "distance": distance}


def compare(lean: dict[str, Any], cert: dict[str, Any]) -> None:
    for name in EXPECTED_STABS:
        if lean["stabilizers"][name] != cert["stabilizers"][name]:
            fail(f"stabilizer {name}: Lean {lean['stabilizers'][name]!r} != certificate {cert['stabilizers'][name]!r}")

    for name in EXPECTED_LOGICALS:
        if lean["logicals"][name] != cert["logicals"][name]:
            fail(f"logical {name}: Lean {lean['logicals'][name]!r} != certificate {cert['logicals'][name]!r}")

    for gid in EXPECTED_GADGETS:
        if lean["gadgets"][gid] != cert["gadgets"][gid]:
            fail(f"gadget {gid}: Lean {lean['gadgets'][gid]!r} != certificate {cert['gadgets'][gid]!r}")

    if lean["distance"] != cert["distance"]:
        fail(f"distance: Lean {lean['distance']!r} != certificate {cert['distance']!r}")


def main(argv: list[str]) -> int:
    root = repo_root()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--lean-file",
        default=root / "QStab" / "QClifford" / "SurfaceD3Distance.lean",
        type=Path,
        help="Lean file that emits the QClifford correspondence JSON",
    )
    parser.add_argument(
        "--certificate",
        default=root / "docs" / "surface_d3_nz_qclifford_geometric_hoare_certificate.json",
        type=Path,
        help="QClifford JSON certificate to compare against",
    )
    args = parser.parse_args(argv)

    try:
        lean = normalize_lean(run_lean_emitter(args.lean_file))
        cert = normalize_certificate(args.certificate)
        compare(lean, cert)
    except (CorrespondenceError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"CORRESPONDENCE FAILED: {exc}", file=sys.stderr)
        return 1

    print("CORRESPONDENCE OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
