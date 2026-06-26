#!/usr/bin/env python3
"""Semantic kernel for the surface-d3 NZ QClifford circuit-distance certificate.

This module is the *non-syntactic* half of the checker.  Where
``check_geometric_hoare.py`` historically only string-matched the assertion
layer, this kernel actually:

  1. Builds the stabilizer group and the centralizer from the certificate's
     declared Pauli generators (F2 / symplectic, from scratch).
  2. Implements the QClifford forward Pauli-propagation transformer ``PropDet``
     (mapCX / mapH / mapPrep / mapMeas) over q0..q9 and the ``dataOf`` projection.
  3. Discharges three genuine semantic obligations by direct computation:
        OBL-INIT  : clean[]  =>  BI_PAIR              (initiation)
        OBL-STEP  : every concrete single-location fault adds <= 1 dangerous
                    spread in each of the X-row and Z-column directions, modulo
                    the stabilizer group  =>  BI_PAIR is preserved with faults+1.
        OBL-DIST  : the *computed* code distance d* (minimum, over logical
                    representatives, of the stabilizer-reduced dangerous spread)
                    equals the bound D claimed by the certificate.
  4. EVALUATES the certificate's own ``XRowsLe`` / ``ZColsLe`` / ``BI_X`` /
     ``BI_Z`` / ``BI_PAIR`` formula *strings* over a model battery and requires
     them to agree, bit-for-bit, with the operational semantics used in 1-3.
     This is what makes the prover's invariant load-bearing: gutting a formula
     body (e.g. ``XRowsLe := TRUE`` or dropping the ``f<=2`` clause) now makes
     the agreement check fail.

Nothing here trusts a rule name, a premise list, or a rendered .qhl line.
"""

from __future__ import annotations

import re
from typing import Any, Callable


class SemanticError(Exception):
    pass


def _fail(msg: str) -> None:
    raise SemanticError(msg)


# --------------------------------------------------------------------------- #
# Pauli bit-vector layer.  A data Pauli is (x, z) with bit q in {0..8}.
# A physical Pauli (for propagation) uses bits {0..9}; dataOf drops bit 9.
# --------------------------------------------------------------------------- #

NDATA = 9
DATA_MASK = (1 << NDATA) - 1
PAULI_BITS = {"I": (0, 0), "X": (1, 0), "Z": (0, 1), "Y": (1, 1)}


def row_of(q: int) -> int:
    return q // 3


def col_of(q: int) -> int:
    return q % 3


def rowx_spread(x: int) -> int:
    rows = 0
    for q in range(NDATA):
        if (x >> q) & 1:
            rows |= 1 << row_of(q)
    return bin(rows).count("1")


def colz_spread(z: int) -> int:
    cols = 0
    for q in range(NDATA):
        if (z >> q) & 1:
            cols |= 1 << col_of(q)
    return bin(cols).count("1")


def named_to_xz(vec: dict[str, tuple[int, int]]) -> tuple[int, int]:
    """Convert the main checker's {qN:(x,z)} representation to packed ints."""
    x = z = 0
    for q, (xx, zz) in vec.items():
        idx = int(q[1:])
        if idx >= NDATA:
            continue
        if xx:
            x |= 1 << idx
        if zz:
            z |= 1 << idx
    return x, z


# --------------------------------------------------------------------------- #
# QClifford forward propagation (PropDet) over physical qubits q0..q9.
# State is a (x, z) pair over 10 bits.  Conjugation by each gate:
#   CX(c,t): X on control -> X on control,target ; Z on target -> Z on control,target
#   H(q)   : swap x,z at q
#   Prep0/PrepP/MeasZ(q): the residual component at q is cleared
# --------------------------------------------------------------------------- #

_GATE_RE = re.compile(r"^([A-Za-z0-9]+)\((q\d+)(?:,(q\d+))?\)$")


def _qidx(name: str) -> int:
    return int(name[1:])


def propagate(x: int, z: int, suffix: list[str]) -> tuple[int, int]:
    for instr in suffix:
        if instr.startswith("!"):
            continue
        m = _GATE_RE.match(instr)
        if m is None:
            _fail(f"propagate: cannot parse instruction {instr!r}")
        op, a, b = m.group(1), m.group(2), m.group(3)
        if op == "CX":
            c, t = _qidx(a), _qidx(b)
            # X on control copies to target
            if (x >> c) & 1:
                x ^= 1 << t
            # Z on target copies to control
            if (z >> t) & 1:
                z ^= 1 << c
        elif op == "H":
            q = _qidx(a)
            xb, zb = (x >> q) & 1, (z >> q) & 1
            x = (x & ~(1 << q)) | (zb << q)
            z = (z & ~(1 << q)) | (xb << q)
        elif op in ("Prep0", "PrepP", "MeasZ", "MeasX"):
            q = _qidx(a)
            x &= ~(1 << q)
            z &= ~(1 << q)
        else:
            _fail(f"propagate: unknown gate {op!r}")
    return x, z


def data_of(x: int, z: int) -> tuple[int, int]:
    return x & DATA_MASK, z & DATA_MASK


# --------------------------------------------------------------------------- #
# Stabilizer group, centralizer, logical representatives (built from scratch).
# --------------------------------------------------------------------------- #


class Geometry:
    def __init__(self, named: dict[str, dict[str, tuple[int, int]]]):
        self.s = [named_to_xz(named[f"s{i}"]) for i in range(8)]
        self.lx = named_to_xz(named["LX"])
        self.lz = named_to_xz(named["LZ"])
        # stabilizer group: 2^8 products
        self.stab_group: list[tuple[int, int]] = []
        for m in range(256):
            x = z = 0
            for i in range(8):
                if (m >> i) & 1:
                    x ^= self.s[i][0]
                    z ^= self.s[i][1]
            self.stab_group.append((x, z))
        self.stab_set = set(self.stab_group)
        # centralizer: span of stabilizers + LX + LZ (2^10 elements)
        gens = self.s + [self.lx, self.lz]
        cent: set[tuple[int, int]] = set()
        for m in range(1 << len(gens)):
            x = z = 0
            for i in range(len(gens)):
                if (m >> i) & 1:
                    x ^= gens[i][0]
                    z ^= gens[i][1]
            cent.add((x, z))
        self.centralizer = cent
        self.logical_reps = [e for e in cent if e not in self.stab_set]

    def min_rowx(self, x: int) -> int:
        return min(rowx_spread(x ^ sx) for sx, _sz in self.stab_group)

    def min_colz(self, z: int) -> int:
        return min(colz_spread(z ^ sz) for _sx, sz in self.stab_group)

    def bi_pair_impl(self, x: int, z: int, f: int) -> bool:
        return self.min_rowx(x) <= f and self.min_colz(z) <= f


# --------------------------------------------------------------------------- #
# Gadget instruction model (mirrors check_geometric_hoare.gadget_instructions).
# Kept here so this module is independently testable.
# --------------------------------------------------------------------------- #


def gadget_instructions(gadget: dict[str, Any]) -> list[str]:
    order = gadget["order"]
    kind = gadget["kind"]
    if kind == "MeasZStab":
        out = ["!q9", "Prep0(q9)"]
        for q in order:
            out += [f"!{q}", "!q9", f"CX({q},q9)"]
        out += ["!q9", "MeasZ(q9)"]
        return out
    if kind == "MeasXStab":
        out = ["!q9", "PrepP(q9)"]
        for q in order:
            out += ["!q9", f"!{q}", f"CX(q9,{q})"]
        out += ["!q9", "H(q9)", "!q9", "MeasZ(q9)"]
        return out
    _fail(f"unknown gadget kind {kind!r}")
    return []  # unreachable


def deterministic_suffix(instrs: list[str], start: int) -> list[str]:
    return [i for i in instrs[start:] if not i.startswith("!")]


# --------------------------------------------------------------------------- #
# OBLIGATION CHECKS (operational semantics).
# --------------------------------------------------------------------------- #


def check_init(geo: Geometry) -> None:
    if not geo.bi_pair_impl(0, 0, 0):
        _fail("OBL-INIT: clean[] (data=I, faults=0) does not satisfy BI_PAIR")


def check_step(geo: Geometry, cert: dict[str, Any]) -> dict[str, int]:
    """Every single-location fault, on every X/Y/Z branch, propagated through the
    remaining deterministic gadget suffix, must add <= 1 dangerous spread in BOTH
    the X-row and Z-column directions modulo the stabilizer group."""
    sites = 0
    branch_checks = 0
    for gadget in cert["program"]["gadgets"]:
        instrs = gadget_instructions(gadget)
        for k, instr in enumerate(instrs):
            if not instr.startswith("!"):
                continue
            sites += 1
            u = _qidx(instr[1:])
            suffix = deterministic_suffix(instrs, k)
            for p in ("X", "Y", "Z"):
                px, pz = PAULI_BITS[p]
                fx = px << u
                fz = pz << u
                dx, dz = data_of(*propagate(fx, fz, suffix))
                dr = geo.min_rowx(dx)
                dc = geo.min_colz(dz)
                if dr > 1 or dc > 1:
                    _fail(
                        f"OBL-STEP: fault !{('q%d' % u)} branch {p} in {gadget['id']} "
                        f"(suffix offset {k}) propagates to dangerous spread "
                        f"rowX={dr}, colZ={dc} (> 1); schedule does not preserve BI_PAIR"
                    )
                branch_checks += 1
    return {"fault_sites": sites, "fault_branch_checks": branch_checks}


def claimed_distance(cert: dict[str, Any]) -> int:
    atom = cert["assertion_syntax"]["atoms"]["DIST_CIRC_D3"]
    m = re.search(r"(\d+)\s*<=\s*faults\[\]", atom)
    if m is None:
        _fail("OBL-DIST: cannot read the claimed distance bound from DIST_CIRC_D3")
    return int(m.group(1))


def check_distance(geo: Geometry, cert: dict[str, Any]) -> dict[str, int]:
    d_claim = claimed_distance(cert)
    if not geo.logical_reps:
        _fail("OBL-DIST: empty logical-representative set")
    d_star = min(max(geo.min_rowx(x), geo.min_colz(z)) for x, z in geo.logical_reps)
    # Soundness: for every logical rep and every f < d_claim, BI_PAIR must fail.
    for x, z in geo.logical_reps:
        for f in range(d_claim):
            if geo.bi_pair_impl(x, z, f):
                _fail(
                    f"OBL-DIST: a logical representative satisfies BI_PAIR at faults={f} "
                    f"< claimed distance {d_claim}; the distance theorem is FALSE"
                )
    if d_star != d_claim:
        _fail(
            f"OBL-DIST: claimed distance {d_claim} != computed distance {d_star} "
            "(stated bound is not tight / not the true semantic distance)"
        )
    return {"claimed_distance": d_claim, "computed_distance": d_star,
            "logical_representatives": len(geo.logical_reps)}


# --------------------------------------------------------------------------- #
# Assertion-logic EVALUATOR.  Parses the certificate's own formula strings and
# evaluates them over concrete models, so the prover's invariant is load-bearing.
# --------------------------------------------------------------------------- #

_TOKEN_RE = re.compile(
    r"""\s*(?:
        (?P<op>/\\|\\/|->|<=|\.\.)        # multi-char: and, or, implies, le, range
      | (?P<id>[A-Za-z_][A-Za-z0-9_]*(?:\[\])?)
      | (?P<num>\d+)
      | (?P<sym>[()\[\],.=*{}])
    )""",
    re.VERBOSE,
)


def tokenize(s: str) -> list[str]:
    toks: list[str] = []
    i = 0
    while i < len(s):
        if s[i].isspace():
            i += 1
            continue
        m = _TOKEN_RE.match(s, i)
        if not m or m.end() == i:
            _fail(f"tokenize: stuck at {s[i:i+20]!r}")
        toks.append(m.group().strip())
        i = m.end()
    return toks


class Parser:
    """Recursive-descent parser producing a tiny AST of nested tuples."""

    def __init__(self, toks: list[str]):
        self.toks = toks
        self.i = 0

    def peek(self) -> str | None:
        return self.toks[self.i] if self.i < len(self.toks) else None

    def next(self) -> str:
        t = self.toks[self.i]
        self.i += 1
        return t

    def expect(self, t: str) -> None:
        got = self.next()
        if got != t:
            _fail(f"parse: expected {t!r} got {got!r}")

    # Formula precedence: -> (lowest) > \/ > /\ > not > atom
    def formula(self) -> Any:
        return self.p_implies()

    def p_implies(self) -> Any:
        left = self.p_or()
        if self.peek() == "->":
            self.next()
            right = self.p_implies()  # right-assoc
            return ("->", left, right)
        return left

    def p_or(self) -> Any:
        left = self.p_and()
        while self.peek() == "\\/":
            self.next()
            left = ("\\/", left, self.p_and())
        return left

    def p_and(self) -> Any:
        left = self.p_not()
        while self.peek() == "/\\":
            self.next()
            left = ("/\\", left, self.p_not())
        return left

    def p_not(self) -> Any:
        if self.peek() == "not":
            self.next()
            return ("not", self.p_not())
        return self.p_atom()

    def p_atom(self) -> Any:
        t = self.peek()
        if t == "(":
            self.next()
            f = self.formula()
            self.expect(")")
            return self._maybe_cmp(f)
        if t in ("exists", "forall"):
            return self.p_quant()
        if t == "TRUE":
            self.next()
            return ("const", True)
        if t == "FALSE":
            self.next()
            return ("const", False)
        # otherwise a term, optionally a comparison
        term = self.term()
        return self._maybe_cmp(term)

    def _maybe_cmp(self, left: Any) -> Any:
        if self.peek() in ("=", "<="):
            op = self.next()
            right = self.term()
            return ("cmp", op, left, right)
        return left  # boolean-valued term/predicate

    def p_quant(self) -> Any:
        q = self.next()  # exists / forall
        # consume optional "stabilizer mask"
        while self.peek() in ("stabilizer", "mask"):
            self.next()
        var = self.next()
        domain = None
        if self.peek() == "in":
            self.next()
            self.expect("{")
            lo = self.next()
            self.expect("..")
            hi = self.next()
            self.expect("}")
            domain = ("range", int(lo), int(hi))
        self.expect(".")
        body = self.formula()
        return ("quant", q, var, domain, body)

    # Terms: product of factors
    def term(self) -> Any:
        left = self.factor()
        while self.peek() == "*":
            self.next()
            left = ("mul", left, self.factor())
        return left

    def factor(self) -> Any:
        t = self.next()
        if t == "(":
            inner = self.term()
            self.expect(")")
            return inner
        if re.fullmatch(r"\d+", t):
            return ("num", int(t))
        # identifier, possibly a call with (...)
        name = t
        if self.peek() == "(":
            self.next()
            args = []
            if self.peek() != ")":
                args.append(self._arg())
                while self.peek() == ",":
                    self.next()
                    args.append(self._arg())
            self.expect(")")
            return ("call", name, args)
        return ("var", name)

    def _arg(self) -> Any:
        # an argument can be a Pauli char literal (X/Y/Z/I as 2nd arg of single)
        # but we cannot tell syntactically; we parse as a term and resolve later.
        return self.term()


_AST_CACHE: dict[str, Any] = {}


def parse_formula(s: str) -> Any:
    if s not in _AST_CACHE:
        p = Parser(tokenize(s))
        ast = p.formula()
        if p.peek() is not None:
            _fail(f"parse_formula: trailing tokens {p.toks[p.i:]!r} in {s!r}")
        _AST_CACHE[s] = ast
    return _AST_CACHE[s]


class Evaluator:
    """Evaluates parsed assertion-logic ASTs over a concrete model.

    Loaded definitions (from the certificate) are expanded by binding formals;
    a fixed set of kernel primitives is implemented operationally.
    """

    PAULI_CHARS = {"I", "X", "Y", "Z"}

    def __init__(self, geo: Geometry, named: dict[str, dict[str, tuple[int, int]]],
                 formula_defs: dict[str, tuple[list[str], Any]],
                 families: dict[str, dict[int, tuple[str, Any]]] | None = None):
        self.geo = geo
        self.consts = {k: named_to_xz(v) for k, v in named.items()}
        self.formula_defs = formula_defs  # name -> (params, ast)
        self.families = families or {}    # name -> {index -> (qparam, ast)}

    # ---- term evaluation: returns ('pauli',(x,z)) | ('int',n) | ('qubit',i)
    #      | ('mask',m) | ('bool',b) | ('vec',(xb,zb)) | ('pchar',c)
    def ev_term(self, node: Any, env: dict[str, Any]) -> Any:
        tag = node[0]
        if tag == "num":
            return ("int", node[1])
        if tag == "mul":
            a = self.ev_term(node[1], env)
            b = self.ev_term(node[2], env)
            return ("pauli", (a[1][0] ^ b[1][0], a[1][1] ^ b[1][1]))
        if tag == "var":
            return self._resolve(node[1], env)
        if tag == "call":
            return self._call(node[1], node[2], env)
        _fail(f"ev_term: unexpected node {node!r}")

    def _resolve(self, name: str, env: dict[str, Any]) -> Any:
        if name in env:
            return env[name]
        if name in self.PAULI_CHARS:
            return ("pchar", name)
        if name == "I":
            return ("pauli", (0, 0))
        if name == "data[]":
            return env["__data__"]
        if name == "faults[]":
            return env["__faults__"]
        if name in self.consts:
            return ("pauli", self.consts[name])
        _fail(f"eval: unbound name {name!r}")

    def _call(self, name: str, args: list[Any], env: dict[str, Any]) -> Any:
        # index-dispatched ground families, e.g. row(q,0)/row(q,1)/row(q,2)
        if name in self.families:
            qval = self.ev_term(args[0], env)
            idx = self.ev_term(args[1], env)[1]
            fam = self.families[name]
            if idx not in fam:
                _fail(f"{name}: no ground instance for index {idx}")
            qparam, ast = fam[idx]
            child = dict(env)
            child[qparam] = qval
            return ("bool", self.ev_formula(ast, child))
        # kernel primitives
        if name == "q":
            return ("qubit", self.ev_term(args[0], env)[1])
        if name == "single":
            q = self._as_qubit(self.ev_term(args[0], env))
            pc = self.ev_term(args[1], env)
            if pc[0] != "pchar":
                _fail("single: 2nd arg must be a Pauli char")
            px, pz = PAULI_BITS[pc[1]]
            return ("pauli", (px << q, pz << q))
        if name == "stabAt":
            i = self.ev_term(args[0], env)[1]
            return ("pauli", self.geo.s[i])
        if name == "ProdStab":
            m = self._as_mask(self.ev_term(args[0], env))
            x = z = 0
            for i in range(8):
                if (m >> i) & 1:
                    x ^= self.geo.s[i][0]
                    z ^= self.geo.s[i][1]
            return ("pauli", (x, z))
        if name == "maskAt":
            m = self._as_mask(self.ev_term(args[0], env))
            i = self.ev_term(args[1], env)[1]
            return ("bool", bool((m >> i) & 1))
        if name == "vecAt":
            e = self.ev_term(args[0], env)[1]
            q = self._as_qubit(self.ev_term(args[1], env))
            return ("vec", ((e[0] >> q) & 1, (e[1] >> q) & 1))
        if name == "hasX":
            v = self.ev_term(args[0], env)
            return ("bool", bool(v[1][0]))
        if name == "hasZ":
            v = self.ev_term(args[0], env)
            return ("bool", bool(v[1][1]))
        if name == "parity":
            a = self.ev_term(args[0], env)[1]
            b = self.ev_term(args[1], env)[1]
            d = (a[0] & b[1]) ^ (a[1] & b[0])
            return ("int", bin(d).count("1") & 1)
        # defined formula (returns bool)
        if name in self.formula_defs:
            params, ast = self.formula_defs[name]
            if len(params) != len(args):
                _fail(f"{name}: arity mismatch")
            child = dict(env)
            for pn, an in zip(params, args):
                child[pn] = self.ev_term(an, env)
            return ("bool", self.ev_formula(ast, child))
        _fail(f"eval: unknown call {name!r}")

    def _as_qubit(self, v: Any) -> int:
        if v[0] in ("qubit", "int"):
            return v[1]
        _fail(f"expected qubit, got {v!r}")
        return -1

    def _as_mask(self, v: Any) -> int:
        if v[0] in ("mask", "int"):
            return v[1]
        _fail(f"expected mask, got {v!r}")
        return -1

    # ---- formula evaluation: returns bool
    def ev_formula(self, node: Any, env: dict[str, Any]) -> bool:
        tag = node[0]
        if tag == "const":
            return bool(node[1])
        if tag == "not":
            return not self.ev_formula(node[1], env)
        if tag == "/\\":
            return self.ev_formula(node[1], env) and self.ev_formula(node[2], env)
        if tag == "\\/":
            return self.ev_formula(node[1], env) or self.ev_formula(node[2], env)
        if tag == "->":
            return (not self.ev_formula(node[1], env)) or self.ev_formula(node[2], env)
        if tag == "cmp":
            return self._cmp(node[1], node[2], node[3], env)
        if tag == "quant":
            return self._quant(node, env)
        if tag == "var" and node[1] in self.formula_defs:
            params, ast = self.formula_defs[node[1]]
            if params:
                _fail(f"formula {node[1]!r} used with no arguments but expects {params}")
            return self.ev_formula(ast, env)
        if tag in ("call", "var"):
            v = self.ev_term(node, env)
            if v[0] != "bool":
                _fail(f"formula position has non-bool term {node!r} -> {v!r}")
            return v[1]
        _fail(f"ev_formula: unexpected node {node!r}")
        return False

    def _cmp(self, op: str, ln: Any, rn: Any, env: dict[str, Any]) -> bool:
        a = self.ev_term(ln, env)
        b = self.ev_term(rn, env)
        if op == "<=":
            return self._num(a) <= self._num(b)
        # "="
        if a[0] == "pauli" or b[0] == "pauli":
            return a[1] == b[1]
        return self._num(a) == self._num(b)

    def _num(self, v: Any) -> int:
        if v[0] in ("int", "qubit", "mask"):
            return v[1]
        _fail(f"expected numeric, got {v!r}")
        return -1

    def _quant(self, node: Any, env: dict[str, Any]) -> bool:
        _, q, var, domain, body = node
        if domain is not None:
            values: list[Any] = [("int", i) for i in range(domain[1], domain[2] + 1)]
        elif var == "m":
            values = [("mask", m) for m in range(256)]
        elif var == "q":
            values = [("qubit", i) for i in range(NDATA)]
        else:
            _fail(f"quantifier over unsupported variable {var!r}")
        results = []
        for val in values:
            child = dict(env)
            child[var] = val
            results.append(self.ev_formula(body, child))
        return all(results) if q == "forall" else any(results)

    # public: evaluate a named atom/predicate over data=E, faults=f
    def bi_pair_cert(self, x: int, z: int, f: int) -> bool:
        env = {"__data__": ("pauli", (x, z)), "__faults__": ("int", f)}
        params, ast = self.formula_defs["BI_PAIR"]
        return self.ev_formula(ast, env)

    def xrowsle_cert(self, x: int, z: int, f: int) -> bool:
        env = {"E": ("pauli", (x, z)), "f": ("int", f)}
        return self.ev_formula(self.formula_defs["XRowsLe"][1], env)

    def zcolsle_cert(self, x: int, z: int, f: int) -> bool:
        env = {"E": ("pauli", (x, z)), "f": ("int", f)}
        return self.ev_formula(self.formula_defs["ZColsLe"][1], env)


def _load_formula_defs(
    cert: dict[str, Any],
) -> tuple[dict[str, tuple[list[str], Any]], dict[str, dict[int, tuple[str, Any]]]]:
    """Parse the certificate's derived formulas + the BI_* atoms into ASTs.

    Heads whose final argument is a numeric literal (``row(q,0)``, ``col(q,2)``)
    are stored as an index-dispatched *family* keyed by that integer, so the
    three ground instances do not collide.  All other heads are normal
    parameterised definitions.
    """
    syn = cert["assertion_syntax"]
    defs: dict[str, tuple[list[str], Any]] = {}
    families: dict[str, dict[int, tuple[str, Any]]] = {}

    def add(decl: str, body: str) -> None:
        m = re.fullmatch(r"([A-Za-z_]\w*)(?:\(([^)]*)\))?", decl.strip())
        if not m:
            _fail(f"cannot parse definition head {decl!r}")
        name = m.group(1)
        params = [p.strip() for p in m.group(2).split(",")] if m.group(2) else []
        if params and re.fullmatch(r"\d+", params[-1]):
            # ground family instance: NAME(qparam, INDEX)
            if len(params) != 2:
                _fail(f"unexpected ground family head {decl!r}")
            families.setdefault(name, {})[int(params[1])] = (params[0], parse_formula(body))
        else:
            defs[name] = (params, parse_formula(body))

    for decl, body in syn["derived_formulas"].items():
        add(decl, body)
    for atom in ("BI_X", "BI_Z", "BI_PAIR"):
        add(atom, syn["atoms"][atom])
    return defs, families


def check_formula_agreement(geo: Geometry, ev: Evaluator) -> dict[str, int]:
    """Tie the prover's invariant strings to the operational semantics.

    (1) XRowsLe / ZColsLe must equal raw row-X / col-Z spread <= f over a broad
        battery (identity, all single-qubit Paulis, every logical representative,
        every stabilizer-group element).  This is where gutting a clause
        (XRowsLe := TRUE, or dropping ``f<=2``) is caught: a 3-row logical at
        f=2 must make XRowsLe FALSE.
    (2) BI_X / BI_Z / BI_PAIR (which add the existential over stabilizer masks)
        must equal the operational BI_PAIR on a small wiring battery.
    """
    le_battery: list[tuple[int, int]] = [(0, 0)]
    for q in range(NDATA):
        le_battery += [(1 << q, 0), (0, 1 << q), (1 << q, 1 << q)]
    le_battery += list(geo.logical_reps)
    le_battery += list(geo.stab_group)

    le_checks = 0
    for x, z in le_battery:
        for f in range(4):
            if ev.xrowsle_cert(x, z, f) != (rowx_spread(x) <= f):
                _fail(
                    f"FORMULA-AGREEMENT: XRowsLe(E,{f}) at x={x:#05x} disagrees with "
                    f"row-X-spread<= {f}; the row barrier formula is vacuous or wrong"
                )
            if ev.zcolsle_cert(x, z, f) != (colz_spread(z) <= f):
                _fail(
                    f"FORMULA-AGREEMENT: ZColsLe(E,{f}) at z={z:#05x} disagrees with "
                    f"col-Z-spread<= {f}; the column barrier formula is vacuous or wrong"
                )
            le_checks += 2

    pair_battery: list[tuple[int, int]] = [(0, 0)]
    for q in range(NDATA):
        pair_battery += [(1 << q, 0), (0, 1 << q)]
    pair_battery += list(geo.logical_reps[:8])
    pair_checks = 0
    for x, z in pair_battery:
        for f in range(4):
            if ev.bi_pair_cert(x, z, f) != geo.bi_pair_impl(x, z, f):
                _fail(
                    "FORMULA-AGREEMENT: certificate BI_PAIR disagrees with the "
                    f"operational semantics at x={x:#05x},z={z:#05x},faults={f}; the "
                    "stabilizer-reduced invariant is vacuous or wrong"
                )
            pair_checks += 1
    return {"formula_le_checks": le_checks, "formula_pair_checks": pair_checks}


# --------------------------------------------------------------------------- #
# Top-level entry.
# --------------------------------------------------------------------------- #


def verify(cert: dict[str, Any], named: dict[str, dict[str, tuple[int, int]]]) -> dict[str, int]:
    geo = Geometry(named)
    counts: dict[str, int] = {}
    check_init(geo)
    counts.update(check_step(geo, cert))
    counts.update(check_distance(geo, cert))
    defs, families = _load_formula_defs(cert)
    ev = Evaluator(geo, named, defs, families)
    counts.update(check_formula_agreement(geo, ev))
    return counts
