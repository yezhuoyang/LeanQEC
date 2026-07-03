#!/usr/bin/env python3
"""One-command verification suite for the NZ QClifford results
(surface-d3 and the parametric HGP chain through hgp_Safe).

This script runs the real Lean/Python verifiers and a permanent negative
regression battery.  It exits 0 only when all positive checks pass and every
tampered certificate is rejected by the intended checker.
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[1]
LEAN_FILE = ROOT / "QStab" / "QClifford" / "SurfaceD3Distance.lean"
QHL_ASSERTION_SYNTAX_FILE = ROOT / "QStab" / "QHL" / "Assertion" / "Syntax.lean"
QHL_ASSERTION_SEMANTICS_FILE = ROOT / "QStab" / "QHL" / "Assertion" / "Semantics.lean"
CALCULUS_FILE = ROOT / "QStab" / "QClifford" / "Compile" / "Calculus.lean"
PCC_BASIC_FILE = ROOT / "QStab" / "QClifford" / "PCC" / "Basic.lean"
PCC_VCGEN_FILE = ROOT / "QStab" / "QClifford" / "PCC" / "VCGen.lean"
PCC_SURFACE_FILE = ROOT / "QStab" / "QClifford" / "PCC" / "SurfaceD3.lean"
PCC_KNILL_FILE = ROOT / "QStab" / "QClifford" / "PCC" / "SurfaceD3Knill.lean"
PCC_SHOR_FILE = ROOT / "QStab" / "QClifford" / "PCC" / "SurfaceD3Shor.lean"
PCC_SHOR_BASE_FILE = ROOT / "QStab" / "QClifford" / "PCC" / "SurfaceD3ShorBase.lean"
PCC_SHOR_GLOBAL_FILE = ROOT / "QStab" / "QClifford" / "PCC" / "SurfaceD3ShorGlobal.lean"
FAULT_HOARE_FILE = ROOT / "QStab" / "QClifford" / "FaultHoare.lean"
HGP_SAFE_FILE = ROOT / "QStab" / "QClifford" / "Compile" / "HGPNZSafe.lean"
HGP_CHAIN_DIR = ROOT / "QStab" / "QClifford" / "Compile"
TCB_BASELINE_FILE = ROOT / "tools" / "verifier_tcb_baseline.sha256"
CERT_FILE = ROOT / "docs" / "surface_d3_nz_qclifford_geometric_hoare_certificate.json"
EXPECTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
BUILD_TARGETS = [
    "QStab.QHL.Assertion",
    "QStab.QClifford.Knill",
    "QStab.QClifford.Shor",
    "QStab.QClifford.Flag",
    "QStab.QClifford.FlagGeneral",
    "QStab.QClifford.SurfaceD3Distance",
    "QStab.QClifford.Compile.Calculus",
    "QStab.QClifford.PCC.Basic",
    "QStab.QClifford.PCC.VCGen",
    "QStab.QClifford.PCC.SurfaceD3",
    "QStab.QClifford.PCC.SurfaceD3Knill",
    "QStab.QClifford.PCC.SurfaceD3Shor",
    "QStab.QClifford.Compile.HGPNZSafe",
]
FINAL_THEOREMS = [
    "surfaceD3_tolerates_two_faults",
    "surfaceD3_reachable_three_fault_logical",
    "surfaceD3_distance_exact_qclifford",
]
ALLOWED_FDERIV_CONSTRUCTORS = ["F_Nil", "F_Gate", "F_ErrLoc", "F_App", "F_And", "F_Conseq"]
FORBIDDEN_FDERIV_WORDS = {
    "embed",
    "axiomRule",
    "byOperational",
    "Valid",
}
BANNED_AUTHORITATIVE_WORDS = {
    "HDeriv",
    "Exec",
    "mapGate",
    "runSites_preserves_BI_PAIR",
    "invariant_of_circuit_run",
    "surfaceD3_circuit_distance_lower_bound",
    "surfaceD3_circuit_distance_exact",
}
BANNED_LEAN_PATTERNS = [
    r"\bsorry\b",
    r"\badmit\b",
    r"\bsorryAx\b",
    r"\bnative_decide\b",
    r"\bbv_decide\b",
    r"(?m)^\s*axiom\b",
]


@dataclass
class CommandResult:
    returncode: int
    stdout: str
    stderr: str

    @property
    def output(self) -> str:
        return self.stdout + self.stderr


@dataclass
class StepResult:
    name: str
    ok: bool
    detail: str


class VerifyError(Exception):
    pass


def run_cmd(args: list[str], timeout: int = 300) -> CommandResult:
    try:
        proc = subprocess.run(
            args,
            cwd=ROOT,
            text=True,
            capture_output=True,
            timeout=timeout,
        )
    except FileNotFoundError as exc:
        raise VerifyError(f"missing executable: {args[0]!r}") from exc
    except subprocess.TimeoutExpired as exc:
        raise VerifyError(f"timed out after {timeout}s: {' '.join(args)}") from exc
    return CommandResult(proc.returncode, proc.stdout, proc.stderr)


def first_interesting_line(text: str) -> str:
    for line in text.splitlines():
        if line.strip():
            return line.strip()
    return "<no output>"


def load_cert(path: Path = CERT_FILE) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_cert(path: Path, cert: dict[str, Any]) -> None:
    path.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")


def set_bound(cert: dict[str, Any], n: int) -> None:
    cert["assertion_syntax"]["atoms"]["DIST_CIRC_D3"] = (
        f"ZeroDet(det[]) /\\ LogicalAny(data[]) -> {n} <= faults[]"
    )
    cert["goal"]["expanded"] = (
        f"DIST_CIRC_D3 := ZeroDet(det[]) /\\ LogicalAny(data[]) -> {n} <= faults[]"
    )
    for deriv in cert["assertion_derivations"]:
        if deriv.get("id") == "A007":
            deriv["conclusion"] = f"BI_PAIR -> (LogicalAny(data[]) -> {n} <= faults[])"
        if deriv.get("id") == "A008":
            deriv["conclusion"] = (
                f"FULL_INV -> (ZeroDet(det[]) /\\ LogicalAny(data[]) -> {n} <= faults[])"
            )


def replace_formula(cert: dict[str, Any], key: str, old: str, new: str) -> None:
    formulas = cert["assertion_syntax"]["derived_formulas"]
    if old in formulas[key]:
        formulas[key] = formulas[key].replace(old, new)


def check_lake_build() -> str:
    res = run_cmd(["lake", "build", *BUILD_TARGETS], timeout=1800)
    if res.returncode != 0:
        raise VerifyError(first_interesting_line(res.output))
    return "lake build succeeded for QClifford scheme, calculus, surface-d3, and PCC modules"


def check_compile_calculus() -> str:
    text = CALCULUS_FILE.read_text(encoding="utf-8")
    hits: list[str] = []
    for pattern in BANNED_LEAN_PATTERNS:
        m = re.search(pattern, text)
        if m:
            hits.append(f"{pattern!r} at offset {m.start()}")
    if hits:
        raise VerifyError("banned Lean token(s) in Compile.Calculus: " + "; ".join(hits))
    for needle in [
        "inductive Scheme",
        "def compileGadget",
        "def flagMeasZ",
        "def rawMeasZ",
        "erase_compileNZ_x_eq_xCircuit",
        "erase_compileNZ_z_eq_zCircuit",
        "erase_compileKnill_z_eq_knillCircuit",
        "compiledCircuit_eq_C_NZ_D3",
    ]:
        if needle not in text:
            raise VerifyError(f"missing calculus declaration/text: {needle}")

    res = run_cmd(["lake", "env", "lean", str(CALCULUS_FILE)], timeout=240)
    if res.returncode != 0:
        raise VerifyError(first_interesting_line(res.output))
    axioms = parse_axioms(res.output, "compiledCircuit_eq_C_NZ_D3")
    if not axioms.issubset(EXPECTED_AXIOMS):
        raise VerifyError(
            f"compiledCircuit_eq_C_NZ_D3 axioms {sorted(axioms)} contain nonstandard axioms"
        )
    for theorem in [
        "erase_compileNZ_x_eq_xCircuit",
        "erase_compileNZ_z_eq_zCircuit",
        "erase_compileKnill_z_eq_knillCircuit",
    ]:
        thm_axioms = parse_axioms(res.output, theorem)
        if not thm_axioms.issubset(EXPECTED_AXIOMS):
            raise VerifyError(
                f"{theorem} axioms {sorted(thm_axioms)} contain nonstandard axioms"
            )
    return (
        "compileGadget NZ/Knill erases to existing scheme circuits and emits the existing "
        "surface C_NZ_D3 circuit with standard axioms"
    )


def check_pcc_basic() -> str:
    text = PCC_BASIC_FILE.read_text(encoding="utf-8")
    hits: list[str] = []
    for pattern in BANNED_LEAN_PATTERNS:
        m = re.search(pattern, text)
        if m:
            hits.append(f"{pattern!r} at offset {m.start()}")
    if hits:
        raise VerifyError("banned Lean token(s) in PCC Basic: " + "; ".join(hits))

    res = run_cmd(["lake", "env", "lean", str(PCC_BASIC_FILE)], timeout=180)
    if res.returncode != 0:
        raise VerifyError(first_interesting_line(res.output))
    for theorem in [
        "certificate_sound",
        "certificate_sound'",
        "combinerPairFlip_syndrome_zero",
        "combinerSingleFlip_syndrome_one",
    ]:
        axioms = parse_axioms(res.output, theorem)
        if not axioms.issubset(EXPECTED_AXIOMS):
            raise VerifyError(
                f"{theorem} axioms {sorted(axioms)} contain nonstandard axioms"
            )
    for needle in [
        "stabilizerReadout",
        "syndromeBit",
        "allPostselectionFlagsZero",
        "AcceptedBarrierBound",
        "CancellationBenign",
        "DistanceCertificate'",
        "certificate_sound'",
        "combinerPairFlip_syndrome_zero",
        "combinerSingleFlip_syndrome_one",
    ]:
        if needle not in text:
            raise VerifyError(f"missing PCC combiner declaration/text: {needle}")
    return "PCC certificate_sound/certificate_sound' and XOR-combiner teeth build with only standard axioms"


def check_qhl_assertion_backend() -> str:
    syntax = QHL_ASSERTION_SYNTAX_FILE.read_text(encoding="utf-8")
    semantics = QHL_ASSERTION_SEMANTICS_FILE.read_text(encoding="utf-8")
    for label, text in [
        ("QHL Assertion Syntax", syntax),
        ("QHL Assertion Semantics", semantics),
    ]:
        hits: list[str] = []
        for pattern in BANNED_LEAN_PATTERNS:
            m = re.search(pattern, text)
            if m:
                hits.append(f"{pattern!r} at offset {m.start()}")
        if hits:
            raise VerifyError(f"banned Lean token(s) in {label}: " + "; ".join(hits))

    for needle in [
        "| detector : Term P Γ .nat -> Term P Γ .bool",
        "def qcSupported",
    ]:
        if needle not in syntax:
            raise VerifyError(f"missing shared assertion syntax declaration/text: {needle}")
    for needle in [
        "structure AssertionBackend",
        "def qstabBackend",
        "def Term.evalWith",
        "def Formula.evalWith",
        "def Formula.denoteWith",
        "Term.evalWith_qstabBackend",
        "Formula.denoteWith_qstabBackend",
    ]:
        if needle not in semantics:
            raise VerifyError(f"missing shared assertion backend declaration/text: {needle}")

    res = run_cmd(["lake", "build", "QStab.QHL.Assertion"], timeout=300)
    if res.returncode != 0:
        raise VerifyError(first_interesting_line(res.output))
    return "QHL assertion language has detector syntax plus shared backend-parametric semantics"


def check_pcc_vcgen() -> str:
    text = PCC_VCGEN_FILE.read_text(encoding="utf-8")
    hits: list[str] = []
    for pattern in BANNED_LEAN_PATTERNS:
        m = re.search(pattern, text)
        if m:
            hits.append(f"{pattern!r} at offset {m.start()}")
    if hits:
        raise VerifyError("banned Lean token(s) in PCC VCGen: " + "; ".join(hits))

    for needle in [
        "def qcliffordBackend",
        "def Formula.denoteQC",
        "def allFlagsZeroF",
        "structure StabilizerSyntax",
        "structure StabilizerCodeSyntax",
        "structure ExtractionSyntax",
        "structure VCInputSyntax",
        "def VCInputSyntax.toVCInput",
        "structure VCInput",
        "structure VCFormulaReport",
        "inductive VCSlot",
        "def VCSlot.denote",
        "inductive FHoareSkeleton",
        "def frontierSkeleton",
        "def hoareSkeleton",
        "structure GeneratedVCs",
        "def vcgen",
        # barrier-free discharge record (replaces old UnconditionalVCs/PostselectedVCs structures)
        "structure DischargedVCs",
        "abbrev UnconditionalVCs",
        "inductive VCGen",
        "theorem vcgen_sound",
        "slots : List VCSlot",
        "hoare : FHoareSkeleton nq",
        "programEq : (vcgen input).denoteSlot .programEq",
        # barrier-free ftDistance slot (replaces barrier-coupled acceptedBound)
        "ftDistance : (vcgen input).denoteSlot .ftDistance",
        # barrier-method adapter convenience constructors
        "def VCGen.ofDistanceCertificate",
        "def VCGen.ofDistanceCertificate'",
        "theorem ftDistance_of_certificate",
        # Bridge/faithfulness theorems (load-bearing, not decorative)
        "theorem denoteQC_allFlagsZeroF",
        "theorem denoteQC_logicalAnyResidual",
        "theorem denoteQC_failureF",
        "theorem denoteQC_circuitDistanceAny",
        "theorem VCInput.formulaReport_faithful",
        "theorem vcgen_safe_in_assertion_language",
        "theorem hoareSkeleton_sound",
    ]:
        if needle not in text:
            raise VerifyError(f"missing VCGen declaration/text: {needle}")

    res = run_cmd(["lake", "env", "lean", str(PCC_VCGEN_FILE)], timeout=240)
    if res.returncode != 0:
        raise VerifyError(first_interesting_line(res.output))
    # vcgen_sound: the main soundness theorem
    axioms = parse_axioms(res.output, "vcgen_sound")
    if not axioms.issubset(EXPECTED_AXIOMS):
        raise VerifyError(
            f"vcgen_sound axioms {sorted(axioms)} contain nonstandard axioms"
        )
    # Bridge theorems: each shared formula is proven to denote the real QClifford obligation
    bridge_theorems = [
        "VCInput.formulaReport_faithful",
        "vcgen_safe_in_assertion_language",
        "hoareSkeleton_sound",
        "ftDistance_of_certificate",
        "ftDistance_of_certificate'",
    ]
    for thm in bridge_theorems:
        thm_axioms = parse_axioms(res.output, thm)
        if not thm_axioms.issubset(EXPECTED_AXIOMS):
            raise VerifyError(
                f"{thm} axioms {sorted(thm_axioms)} contain nonstandard axioms"
            )
    return (
        "VCGen barrier-free interface: DischargedVCs/ftDistance slot, vcgen_sound, "
        "bridge/faithfulness theorems, and adapter lemmas all build with standard axioms"
    )


def check_pcc_surface() -> str:
    text = PCC_SURFACE_FILE.read_text(encoding="utf-8")
    hits: list[str] = []
    for pattern in BANNED_LEAN_PATTERNS:
        m = re.search(pattern, text)
        if m:
            hits.append(f"{pattern!r} at offset {m.start()}")
    if hits:
        raise VerifyError("banned Lean token(s) in PCC SurfaceD3: " + "; ".join(hits))
    if "def surfaceD3Cert" not in text:
        raise VerifyError("missing closed surfaceD3Cert")
    for needle in [
        "def surfaceD3SyntaxInput",
        "abbrev surfaceD3GeneratedVCs",
        "surfaceD3GeneratedVCs.slots",
        "surfaceD3GeneratedVCs.hoare",
        "def surfaceD3SyntaxDischarge",
        "def surfaceD3SyntaxVCGen",
        "vcgen_sound surfaceD3SyntaxVCGen",
        "surfaceD3_safe_from_syntax",
        "def surfaceD3Input",
        "def surfaceD3VCGen",
        "VCGen.ofDistanceCertificate surfaceD3Cert",
        "vcgen_sound surfaceD3VCGen",
        "surfaceD3_safe_vcgen",
    ]:
        if needle not in text:
            raise VerifyError(f"surfaceD3_safe is not routed through VCGen: missing {needle}")

    res = run_cmd(["lake", "env", "lean", str(PCC_SURFACE_FILE)], timeout=900)
    if res.returncode != 0:
        raise VerifyError(first_interesting_line(res.output))
    axioms = parse_axioms(res.output, "surfaceD3_safe")
    if axioms != EXPECTED_AXIOMS:
        raise VerifyError(f"surfaceD3_safe axioms {sorted(axioms)} != {sorted(EXPECTED_AXIOMS)}")
    return "surfaceD3 PCC client closes through VCGen/vcgen_sound with standard axioms"


def check_surface_syntax_bad_syn_rejected() -> str:
    tmp_dir = Path(tempfile.mkdtemp(prefix="leanqec_pcc_bad_syntax_syn_"))
    try:
        bad_file = tmp_dir / "BadSurfaceSyntaxSyn.lean"
        bad_file.write_text(
            """
import QStab.QClifford.PCC.SurfaceD3

namespace QStab.QClifford.PCC.SurfaceD3

example : (vcgen surfaceD3SyntaxInput.toVCInput).denoteSlot .syn := by
  intro i E
  rfl

end QStab.QClifford.PCC.SurfaceD3
""".lstrip(),
            encoding="utf-8",
        )
        res = run_cmd(["lake", "env", "lean", str(bad_file)], timeout=240)
        if res.returncode == 0:
            raise VerifyError("bogus rfl proof discharged the generated syndrome VC")
        if (
            "rfl" not in res.output
            and "failed" not in res.output.lower()
            and "unsolved goals" not in res.output
        ):
            raise VerifyError(
                "bad generated syndrome proof failed for an unexpected reason: "
                + first_interesting_line(res.output)
            )
        return "bogus rfl proof is rejected by the generated syndrome-correctness VC"
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)


def check_pcc_knill() -> str:
    text = PCC_KNILL_FILE.read_text(encoding="utf-8")
    hits: list[str] = []
    for pattern in BANNED_LEAN_PATTERNS:
        m = re.search(pattern, text)
        if m:
            hits.append(f"{pattern!r} at offset {m.start()}")
    if hits:
        raise VerifyError("banned Lean token(s) in PCC SurfaceD3Knill: " + "; ".join(hits))
    for needle in [
        "def knillCert",
        "def surfaceD3KnillInput",
        "def surfaceD3KnillVCGen",
        "VCGen.ofDistanceCertificate knillCert",
        "vcgen_sound surfaceD3KnillVCGen",
        "stabilizerReadout := readout",
        "theorem surfaceSyn",
        "theorem surfaceD3_knill_safe",
    ]:
        if needle not in text:
            raise VerifyError(f"missing Knill PCC declaration/text: {needle}")

    res = run_cmd(["lake", "build", "QStab.QClifford.PCC.SurfaceD3Knill"], timeout=1800)
    if res.returncode != 0:
        raise VerifyError(first_interesting_line(res.output))
    axioms = parse_axioms(res.output, "surfaceD3_knill_safe")
    if axioms != EXPECTED_AXIOMS:
        raise VerifyError(
            f"surfaceD3_knill_safe axioms {sorted(axioms)} != {sorted(EXPECTED_AXIOMS)}"
        )
    return "Knill surface-d3 PCC client closes through VCGen/vcgen_sound with standard axioms"


def check_pcc_shor_skeleton() -> str:
    shor_files = [PCC_SHOR_FILE, PCC_SHOR_BASE_FILE, PCC_SHOR_GLOBAL_FILE]
    text = ""
    for f in shor_files:
        part = f.read_text(encoding="utf-8")
        for pattern in BANNED_LEAN_PATTERNS:
            m = re.search(pattern, part)
            if m:
                raise VerifyError(
                    f"banned Lean token {pattern!r} in {f.name} at offset {m.start()}"
                )
        text += part
    for needle in [
        "def shorSurfaceCircuit",
        "def surfaceSpecShor",
        "def surfaceBarrier",
        "def surfaceAcceptedBarrierBound",
        "def fcevalW_linear",
        "def detected_group_le",
        "def accepted_contribution_partition_bound",
        "theorem dangerousSpread_subadditive",
        "theorem benign_spread_le",
        "theorem dangerous_branch_fires",
        "theorem benign_contribution_product_le_length",
        "theorem surfaceAcceptedBarrierBound_of_ladder",
        "theorem shor4_full_hook_pair_trueWeight_zero",
    ]:
        if needle not in text:
            raise VerifyError(f"missing Shor PCC skeleton declaration/text: {needle}")
    if re.search(r"\btheorem\s+surfaceD3_shor_safe\b", text):
        raise VerifyError("SurfaceD3Shor claims surfaceD3_shor_safe without closing AcceptedBarrierBound")

    res = run_cmd(["lake", "build", "QStab.QClifford.PCC.SurfaceD3Shor"], timeout=900)
    if res.returncode != 0:
        raise VerifyError(first_interesting_line(res.output))
    if "surfaceAcceptedBarrierBound : Prop" not in res.output:
        raise VerifyError("missing #check output for surfaceAcceptedBarrierBound")
    for theorem in [
        "shor4_full_hook_pair_trueWeight_zero",
        "dangerousSpread_subadditive",
        "benign_spread_le",
        "dangerous_branch_fires",
        "benign_contribution_product_le_length",
        "surfaceAcceptedBarrierBound_of_ladder",
    ]:
        axioms = parse_axioms(res.output, theorem)
        if not axioms.issubset(EXPECTED_AXIOMS):
            raise VerifyError(
                f"{theorem} axioms {sorted(axioms)} contain nonstandard axioms"
            )
    return (
        "Shor PCC skeleton compiles, pins AcceptedBarrierBound as the remaining "
        "producer obligation, and checks the closed L1/L3 ladder rungs"
    )


def check_fderiv_rules_only() -> str:
    text = FAULT_HOARE_FILE.read_text(encoding="utf-8")
    m = re.search(r"(?ms)^inductive\s+FDeriv\b(?P<body>.*?)(?=^/-! ## Inversion lemmas\b)", text)
    if not m:
        raise VerifyError("could not locate QClifford FDeriv inductive block")
    block = m.group("body")
    constructors = re.findall(r"(?m)^\s*\|\s+([A-Za-z_][A-Za-z0-9_']*)\b", block)
    if constructors != ALLOWED_FDERIV_CONSTRUCTORS:
        raise VerifyError(
            f"FDeriv constructors {constructors} != {ALLOWED_FDERIV_CONSTRUCTORS}"
        )
    forbidden_hits = sorted(
        word for word in FORBIDDEN_FDERIV_WORDS
        if re.search(rf"\b{re.escape(word)}\b", block)
    )
    if forbidden_hits:
        raise VerifyError("forbidden FDeriv word(s): " + ", ".join(forbidden_hits))
    return "QClifford FDeriv constructors are exactly F_Nil/F_Gate/F_ErrLoc/F_App/F_And/F_Conseq"


def check_qclifford_authoritative_shape() -> str:
    text = LEAN_FILE.read_text(encoding="utf-8")
    hits = sorted(
        word for word in BANNED_AUTHORITATIVE_WORDS
        if re.search(rf"\b{re.escape(word)}\b", text)
    )
    if hits:
        raise VerifyError("authoritative QClifford proof mentions banned bespoke stack word(s): " + ", ".join(hits))

    if "def surfaceD3Deriv : FDeriv cleanPre C_NZ_D3 distPost" not in text:
        raise VerifyError("surfaceD3Deriv is not declared with the expected FDeriv type")
    if "fhoare_sound surfaceD3Deriv" not in text:
        raise VerifyError("surfaceD3 Hoare theorem is not obtained through fhoare_sound surfaceD3Deriv")
    if "toleratesFaultsΛ_of_hoare C_NZ_D3 logicalFailure 2 surfaceD3_hoare" not in text:
        raise VerifyError("surfaceD3_tolerates_two_faults is not obtained through toleratesFaultsΛ_of_hoare")
    return "surfaceD3Deriv is a QClifford FDeriv and the authoritative file does not mention HDeriv/Exec/mapGate"


def check_hgp_chain() -> str:
    hgp_files = sorted(HGP_CHAIN_DIR.glob("HGPNZ*.lean"))
    if len(hgp_files) < 5:
        raise VerifyError(f"expected the HGPNZ chain files, found only {len(hgp_files)}")
    for f in hgp_files:
        text = f.read_text(encoding="utf-8")
        for pattern in BANNED_LEAN_PATTERNS:
            m = re.search(pattern, text)
            if m:
                raise VerifyError(
                    f"banned Lean token {pattern!r} in {f.name} at offset {m.start()}"
                )
    text = HGP_SAFE_FILE.read_text(encoding="utf-8")
    for needle in [
        "def hgp_Safe (d : Nat) (hd : 2 ≤ d) :",
        "DischargedVCs (generatedFullProgramVCInputD (hgpXZProgram d) d",
        "reachScript := hgpReachScript d hd",
        "theorem hgp_compiled_Safe (d : Nat) (hd : 2 ≤ d) :",
        "Safe (compileProgram (hgpXZProgram d))",
        "vcgen_sound (.mk (hgp_Safe d hd))",
    ]:
        if needle not in text:
            raise VerifyError(f"missing HGP capstone declaration/text: {needle}")
    probe = ROOT / "tools" / "_verify_hgp_probe.lean"
    probe.write_text(
        "import QStab.QClifford.Compile.HGPNZSafe" + chr(10)
        + "#print axioms QStab.QClifford.Compile.hgp_Safe" + chr(10)
        + "#print axioms QStab.QClifford.Compile.hgp_compiled_Safe" + chr(10),
        encoding="utf-8",
    )
    try:
        res = run_cmd(["lake", "env", "lean", str(probe)], timeout=300)
        if res.returncode != 0:
            raise VerifyError(first_interesting_line(res.output))
        for thm in ["hgp_Safe", "hgp_compiled_Safe"]:
            axioms = parse_axioms(res.output, thm)
            if axioms != EXPECTED_AXIOMS:
                raise VerifyError(
                    f"{thm} axioms {sorted(axioms)} != {sorted(EXPECTED_AXIOMS)}"
                )
    finally:
        probe.unlink(missing_ok=True)
    return (
        "HGP chain: banned-token battery clean over HGPNZ*, hgp_Safe/hgp_compiled_Safe "
        "declaration shapes present, both capstone headliners close with standard axioms"
    )


def check_tcb_baseline() -> str:
    import hashlib

    lines = [
        ln.strip()
        for ln in TCB_BASELINE_FILE.read_text(encoding="utf-8").splitlines()
        if ln.strip()
    ]
    if len(lines) < 5:
        raise VerifyError(f"TCB baseline lists {len(lines)} files, expected at least 5")
    for ln in lines:
        want, sep, rel = ln.partition(" *")
        if not sep:
            raise VerifyError(f"malformed TCB baseline line: {ln!r}")
        target = ROOT / rel.strip()
        if not target.exists():
            raise VerifyError(f"TCB-pinned file missing: {rel.strip()}")
        got = hashlib.sha256(target.read_bytes()).hexdigest()
        if got != want.strip():
            raise VerifyError(f"TCB hash mismatch for {rel.strip()}")
    return f"TCB baseline verified ({len(lines)} pinned verifier files match)"


def parse_axioms(output: str, theorem: str) -> set[str]:
    pat = re.compile(
        rf"'[^']*{re.escape(theorem)}'\s+depends on axioms:\s*\[(.*?)\]",
        re.DOTALL,
    )
    matches = pat.findall(output)
    if not matches:
        raise VerifyError(f"missing #print axioms output for {theorem}")
    return {part.strip() for part in matches[-1].replace("\n", " ").split(",") if part.strip()}


def check_axiom_hygiene() -> str:
    text = LEAN_FILE.read_text(encoding="utf-8")
    hits: list[str] = []
    for pattern in BANNED_LEAN_PATTERNS:
        m = re.search(pattern, text)
        if m:
            hits.append(f"{pattern!r} at offset {m.start()}")
    if hits:
        raise VerifyError("banned Lean token(s): " + "; ".join(hits))

    res = run_cmd(["lake", "env", "lean", str(LEAN_FILE)], timeout=240)
    if res.returncode != 0:
        raise VerifyError(first_interesting_line(res.output))
    if "surfaceD3Deriv : FDeriv cleanPre C_NZ_D3 distPost" not in res.output:
        raise VerifyError("missing #check output showing surfaceD3Deriv has type FDeriv")
    for theorem in FINAL_THEOREMS:
        axioms = parse_axioms(res.output, theorem)
        if axioms != EXPECTED_AXIOMS:
            raise VerifyError(f"{theorem} axioms {sorted(axioms)} != {sorted(EXPECTED_AXIOMS)}")
    return "QClifford final theorem axioms are exactly [Classical.choice, Quot.sound, propext], and #check shows surfaceD3Deriv : FDeriv"


def check_geometric_positive() -> str:
    res = run_cmd([sys.executable, "tools/check_geometric_hoare.py"], timeout=180)
    out = res.output
    if res.returncode != 0 or "CHECK PASSED" not in out:
        raise VerifyError(first_interesting_line(out))
    claimed = re.search(r"claimed_distance:\s*(\d+)", out)
    computed = re.search(r"computed_distance:\s*(\d+)", out)
    if not claimed or not computed:
        raise VerifyError("missing claimed_distance/computed_distance in checker output")
    if claimed.group(1) != "3" or computed.group(1) != "3":
        raise VerifyError(
            f"distance mismatch: claimed={claimed.group(1)}, computed={computed.group(1)}"
        )
    return "check_geometric_hoare.py passed with computed_distance=claimed_distance=3"


def check_correspondence_positive() -> str:
    res = run_cmd([sys.executable, "tools/check_lean_cert_correspondence.py"], timeout=180)
    if res.returncode != 0 or "CORRESPONDENCE OK" not in res.output:
        raise VerifyError(first_interesting_line(res.output))
    return "Lean/certificate correspondence is OK"


def check_trivial_barrier_rejected() -> str:
    tmp_dir = Path(tempfile.mkdtemp(prefix="leanqec_pcc_bad_barrier_"))
    try:
        bad_file = tmp_dir / "BadBarrier.lean"
        bad_file.write_text(
            """
import QStab.QClifford.PCC.SurfaceD3

namespace QStab.QClifford.PCC.SurfaceD3

def badTrivialBarrierCert :
    DistanceCertificate QStab.QClifford.SurfaceD3Distance.C_NZ_D3 surfaceSpec where
  barrier := fun _ => 0
  programEq := surfaceProgramEq
  wf := surfaceWF
  syn := surfaceSyn
  init := rfl
  step := by
    intro i site hmem es p hp
    simp [SiteSafeβ]
  preserve := by
    intro i es
    rfl
  dist := by
    intro es hFail
    simp [surfaceSpec]
  reachScript := QStab.QClifford.SurfaceD3Distance.reachLogicalXScript
  reachOk := surfaceReachOk

end QStab.QClifford.PCC.SurfaceD3
""".lstrip(),
            encoding="utf-8",
        )
        res = run_cmd(["lake", "env", "lean", str(bad_file)], timeout=240)
        if res.returncode == 0:
            raise VerifyError("trivial barrier certificate was accepted")
        if "unsolved goals" not in res.output and "failed" not in res.output.lower():
            raise VerifyError("trivial barrier failed for an unexpected reason: " + first_interesting_line(res.output))
        return "trivial barrier certificate is rejected by the generated dist VC"
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)


def check_wrong_flag_mapping_rejected() -> str:
    tmp_dir = Path(tempfile.mkdtemp(prefix="leanqec_pcc_bad_flag_"))
    try:
        bad_file = tmp_dir / "BadFlagSlot.lean"
        bad_file.write_text(
            """
import QStab.QClifford.PCC.SurfaceD3

namespace QStab.QClifford.PCC.SurfaceD3

def badFlagSlotSpec : CodeSpec 10 :=
  { surfaceSpec with
    flagSlot := fun _ => 0
    flagSlot_injective := by
      intro a b h
      exact Fin.ext h
    flagSlot_ordered := by
      intro i
      rfl }

def badFlagSlotCert :
    DistanceCertificate QStab.QClifford.SurfaceD3Distance.C_NZ_D3 badFlagSlotSpec where
  barrier := surfaceBarrier
  programEq := by
    simpa [badFlagSlotSpec] using surfaceProgramEq
  wf := by
    simpa [badFlagSlotSpec] using surfaceWF
  syn := by
    intro i E
    exact surfaceSyn i E
  init := surfaceInit
  step := by
    simpa [badFlagSlotSpec] using surfaceStep
  preserve := by
    simpa [badFlagSlotSpec] using surfacePreserve
  dist := by
    simpa [badFlagSlotSpec] using surfaceDist
  reachScript := QStab.QClifford.SurfaceD3Distance.reachLogicalXScript
  reachOk := by
    simpa [badFlagSlotSpec] using surfaceReachOk

end QStab.QClifford.PCC.SurfaceD3
""".lstrip(),
            encoding="utf-8",
        )
        res = run_cmd(["lake", "env", "lean", str(bad_file)], timeout=240)
        if res.returncode == 0:
            raise VerifyError("wrong flag-slot mapping certificate was accepted")
        return "non-injective flag-slot mapping is rejected by the generated CodeSpec VC"
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)


def check_overflag_reach_rejected() -> str:
    tmp_dir = Path(tempfile.mkdtemp(prefix="leanqec_pcc_overflag_"))
    try:
        bad_file = tmp_dir / "BadOverFlagReach.lean"
        bad_file.write_text(
            """
import QStab.QClifford.PCC.SurfaceD3

namespace QStab.QClifford.PCC.SurfaceD3

def overFlagScript : List (Option Pauli) :=
  (List.range (QStab.Paper.SurfaceD3CircuitDistance.C_NZ_D3_sites.length)).map fun i =>
    if i = 9 then some Pauli.X else none

example :
    (QStab.QClifford.PCC.runFScript QStab.QClifford.SurfaceD3Distance.C_NZ_D3
      overFlagScript (ErrorState.clean 10)).1.detectors 0 = true := by
  unfold overFlagScript QStab.QClifford.PCC.runFScript
  unfold QStab.QClifford.SurfaceD3Distance.C_NZ_D3
    QStab.QClifford.SurfaceD3Distance.G0 QStab.QClifford.SurfaceD3Distance.G1
    QStab.QClifford.SurfaceD3Distance.G2 QStab.QClifford.SurfaceD3Distance.G3
    QStab.QClifford.SurfaceD3Distance.G4 QStab.QClifford.SurfaceD3Distance.G5
    QStab.QClifford.SurfaceD3Distance.G6 QStab.QClifford.SurfaceD3Distance.G7
    QStab.QClifford.SurfaceD3Distance.zGadget
    QStab.QClifford.SurfaceD3Distance.xGadget
    QStab.QClifford.SurfaceD3Distance.G0Order
    QStab.QClifford.SurfaceD3Distance.G1Order
    QStab.QClifford.SurfaceD3Distance.G2Order
    QStab.QClifford.SurfaceD3Distance.G3Order
    QStab.QClifford.SurfaceD3Distance.G4Order
    QStab.QClifford.SurfaceD3Distance.G5Order
    QStab.QClifford.SurfaceD3Distance.G6Order
    QStab.QClifford.SurfaceD3Distance.G7Order
    QStab.QClifford.SurfaceD3Distance.qq
    QStab.QClifford.SurfaceD3Distance.dq
    QStab.QClifford.SurfaceD3Distance.physOfData
  decide

def badOverFlagReachCert :
    DistanceCertificate QStab.QClifford.SurfaceD3Distance.C_NZ_D3 surfaceSpec where
  barrier := surfaceBarrier
  programEq := surfaceProgramEq
  wf := surfaceWF
  syn := surfaceSyn
  init := surfaceInit
  step := surfaceStep
  preserve := surfacePreserve
  dist := surfaceDist
  reachScript := overFlagScript
  reachOk := by
    decide

end QStab.QClifford.PCC.SurfaceD3
""".lstrip(),
            encoding="utf-8",
        )
        res = run_cmd(["lake", "env", "lean", str(bad_file)], timeout=300)
        if res.returncode == 0:
            raise VerifyError("over-flagged reachability witness was accepted")
        if (
            "reachOk" not in res.output
            and "failed" not in res.output.lower()
            and "unsolved goals" not in res.output
            and "Tactic `decide`" not in res.output
        ):
            raise VerifyError(
                "over-flagged reach witness failed for an unexpected reason: "
                + first_interesting_line(res.output)
            )
        return "reachScript witness that fires a flag is rejected by the reachOk VC"
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)


def check_two_detector_regression() -> str:
    tmp_dir = Path(tempfile.mkdtemp(prefix="leanqec_pcc_two_detector_"))
    try:
        check_file = tmp_dir / "TwoDetectorRegression.lean"
        check_file.write_text(
            """
import QStab.QClifford.PCC.SurfaceD3

namespace QStab.QClifford.PCC.SurfaceD3

example : ¬ undetected surfaceSpec twoDetectorFireState :=
  surfaceTwoDetector_not_undetected

#print axioms surfaceTwoDetector_not_undetected

end QStab.QClifford.PCC.SurfaceD3
""".lstrip(),
            encoding="utf-8",
        )
        res = run_cmd(["lake", "env", "lean", str(check_file)], timeout=240)
        if res.returncode != 0:
            raise VerifyError(first_interesting_line(res.output))
        axioms = parse_axioms(res.output, "surfaceTwoDetector_not_undetected")
        if not axioms.issubset(EXPECTED_AXIOMS):
            raise VerifyError(
                f"surfaceTwoDetector_not_undetected axioms {sorted(axioms)} contain nonstandard axioms"
            )
        return "two fired detector slots imply not undetected"
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)


def mutate_bad_cnot_order(cert: dict[str, Any]) -> None:
    for gadget in cert["program"]["gadgets"]:
        if gadget["id"] == "G1":
            gadget["order"] = ["q1", "q4", "q2", "q5"]
            return


def mutate_drop_distance_clause(cert: dict[str, Any]) -> None:
    replace_formula(
        cert,
        "XRowsLe(E,f)",
        "(f<=2 -> not XRowsAll(E))",
        "(f<=99 -> TRUE)",
    )


def mutate_xrows_true(cert: dict[str, Any]) -> None:
    cert["assertion_syntax"]["derived_formulas"]["XRowsLe(E,f)"] = "TRUE"


def mutate_a007_zero(cert: dict[str, Any]) -> None:
    for deriv in cert["assertion_derivations"]:
        if deriv.get("id") == "A007":
            deriv["conclusion"] = "BI_PAIR -> (LogicalAny(data[]) -> 0 <= faults[])"
            return


def mutate_overclaim_d4(cert: dict[str, Any]) -> None:
    set_bound(cert, 4)


def mutate_underclaim_d2(cert: dict[str, Any]) -> None:
    set_bound(cert, 2)


def mutate_cert_s0_support(cert: dict[str, Any]) -> None:
    term = cert["assertion_syntax"]["derived_terms"]["s0"]
    cert["assertion_syntax"]["derived_terms"]["s0"] = term.replace(
        "single(q4,Z)", "single(q5,Z)"
    )


def mutate_cert_gadget_order(cert: dict[str, Any]) -> None:
    for gadget in cert["program"]["gadgets"]:
        if gadget["id"] == "G1":
            gadget["order"] = ["q1", "q4", "q2", "q5"]
            return


def mutate_cert_lx_support(cert: dict[str, Any]) -> None:
    term = cert["assertion_syntax"]["derived_terms"]["LX"]
    cert["assertion_syntax"]["derived_terms"]["LX"] = term.replace(
        "single(q6,X)", "single(q7,X)"
    )


def mutate_cert_bound_only(cert: dict[str, Any]) -> None:
    cert["assertion_syntax"]["atoms"]["DIST_CIRC_D3"] = (
        "ZeroDet(det[]) /\\ LogicalAny(data[]) -> 4 <= faults[]"
    )


def write_tampered_cert(tempdir: Path, label: str, mutate: Callable[[dict[str, Any]], None]) -> Path:
    cert = load_cert()
    mutate(cert)
    path = tempdir / (re.sub(r"[^A-Za-z0-9_.-]+", "_", label).strip("_") + ".json")
    write_cert(path, cert)
    return path


def check_geometric_rejection(
    tempdir: Path,
    label: str,
    mutate: Callable[[dict[str, Any]], None],
    reason: str,
) -> str:
    path = write_tampered_cert(tempdir, label, mutate)
    res = run_cmd([sys.executable, "tools/check_geometric_hoare.py", str(path)], timeout=180)
    out = res.output
    if res.returncode == 0 or "CHECK FAILED" not in out:
        raise VerifyError(f"tamper was accepted: {first_interesting_line(out)}")
    if reason not in out:
        raise VerifyError(f"tamper rejected, but output did not contain {reason!r}")
    return f"rejected with {reason}"


def check_correspondence_rejection(
    tempdir: Path,
    label: str,
    mutate: Callable[[dict[str, Any]], None],
    reason: str,
) -> str:
    path = write_tampered_cert(tempdir, label, mutate)
    res = run_cmd(
        [sys.executable, "tools/check_lean_cert_correspondence.py", "--certificate", str(path)],
        timeout=180,
    )
    out = res.output
    if res.returncode == 0 or "CORRESPONDENCE FAILED" not in out:
        raise VerifyError(f"tamper was accepted: {first_interesting_line(out)}")
    if reason not in out:
        raise VerifyError(f"tamper rejected, but output did not contain {reason!r}")
    return f"rejected with {reason}"


def run_step(name: str, fn: Callable[[], str]) -> StepResult:
    try:
        detail = fn()
        result = StepResult(name, True, detail)
        print(f"PASS {name}: {detail}")
        return result
    except Exception as exc:
        result = StepResult(name, False, str(exc))
        print(f"FAIL {name}: {exc}")
        return result


def main() -> int:
    results: list[StepResult] = []
    tempdir = Path(tempfile.mkdtemp(prefix="leanqec_surface_d3_verify_"))
    try:
        positive_steps: list[tuple[str, Callable[[], str]]] = [
            ("positive/fderiv-rules-only", check_fderiv_rules_only),
            ("positive/qclifford-authoritative-shape", check_qclifford_authoritative_shape),
            ("positive/compile-calculus", check_compile_calculus),
            ("positive/pcc-basic", check_pcc_basic),
            ("positive/qhl-assertion-backend", check_qhl_assertion_backend),
            ("positive/pcc-vcgen", check_pcc_vcgen),
            ("positive/pcc-surface", check_pcc_surface),
            ("positive/pcc-knill", check_pcc_knill),
            ("positive/pcc-shor-skeleton", check_pcc_shor_skeleton),
            ("positive/lake-build", check_lake_build),
            ("positive/hgp-chain", check_hgp_chain),
            ("positive/tcb-baseline", check_tcb_baseline),
            ("positive/axiom-hygiene", check_axiom_hygiene),
            ("positive/geometric-hoare", check_geometric_positive),
            ("positive/lean-cert-correspondence", check_correspondence_positive),
        ]
        for name, fn in positive_steps:
            results.append(run_step(name, fn))

        geometric_tampers = [
            ("negative/geometric/bad-cnot-order", mutate_bad_cnot_order, "dangerous spread"),
            ("negative/geometric/drop-f<=2-clause", mutate_drop_distance_clause,
             "FORMULA-AGREEMENT"),
            ("negative/geometric/xrowsle-true", mutate_xrows_true, "FORMULA-AGREEMENT"),
            ("negative/geometric/a007-bound-0", mutate_a007_zero, "A007"),
            ("negative/geometric/consistent-d4", mutate_overclaim_d4, "OBL-DIST"),
            ("negative/geometric/consistent-d2", mutate_underclaim_d2, "claimed distance 2"),
        ]
        for name, mutate, reason in geometric_tampers:
            results.append(run_step(
                name,
                lambda mutate=mutate, name=name, reason=reason:
                    check_geometric_rejection(tempdir, name, mutate, reason),
            ))

        correspondence_tampers = [
            ("negative/correspondence/cert-s0-support", mutate_cert_s0_support, "stabilizer s0"),
            ("negative/correspondence/cert-g1-order", mutate_cert_gadget_order, "gadget G1"),
            ("negative/correspondence/cert-lx-support", mutate_cert_lx_support, "logical LX"),
            ("negative/correspondence/cert-bound", mutate_cert_bound_only, "distance"),
        ]
        for name, mutate, reason in correspondence_tampers:
            results.append(run_step(
                name,
                lambda mutate=mutate, name=name, reason=reason:
                    check_correspondence_rejection(tempdir, name, mutate, reason),
            ))

        results.append(run_step(
            "negative/pcc/trivial-barrier",
            check_trivial_barrier_rejected,
        ))
        results.append(run_step(
            "negative/pcc/wrong-flag-slot-mapping",
            check_wrong_flag_mapping_rejected,
        ))
        results.append(run_step(
            "negative/pcc/overflag-reach-witness",
            check_overflag_reach_rejected,
        ))
        results.append(run_step(
            "negative/pcc/two-detector-undetected",
            check_two_detector_regression,
        ))
        results.append(run_step(
            "negative/vcgen/bad-syndrome-proof",
            check_surface_syntax_bad_syn_rejected,
        ))
    finally:
        shutil.rmtree(tempdir, ignore_errors=True)

    failed = [result for result in results if not result.ok]
    print()
    print(f"SUMMARY: {len(results) - len(failed)} passed, {len(failed)} failed")
    if failed:
        print("VERIFICATION FAILED")
        return 1
    print("ALL VERIFICATIONS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
