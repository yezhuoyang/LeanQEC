#!/usr/bin/env bash
# Surface-code distance verification audit (run from repo root).
# Auditor-side tool: it does NOT prove anything; it checks the prover's work.
# "PERFECT" requires every section below to pass.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT" || exit 2
# Portable paths: override BASELINE via $SURFACE_AUDIT_BASELINE; default is repo-relative
# (works in any shell, unlike a hardcoded /c/tmp).
BASELINE="${SURFACE_AUDIT_BASELINE:-$ROOT/tools/surface_audit_baseline.sha256}"
TMPDIR_AUDIT="$ROOT/tools/.audit-tmp"
mkdir -p "$TMPDIR_AUDIT" 2>/dev/null
LOG="$TMPDIR_AUDIT/audit_build.log"
FROZEN=(
  QStab/QHL/CodeLang.lean QStab/QHL/CodeLogic.lean QStab/QHL/CodeRules.lean
  QStab/QHL/CodeAlgebra.lean QStab/QHL/CodeNatArithmetic.lean QStab/QHL/CodeDerivation.lean
  QStab/QHL/CodeStabBinder.lean QStab/QHL/CodeSurface.lean
  QStab/QHL/Verify/CodeEvalHelpers.lean QStab/QHL/Verify/PureDeriv.lean
  QStab/QHL/Verify/SurfaceDistanceContract.lean QStab/QHL/Verify/SurfaceDistanceAudit.lean
)
fail=0

echo "== [1] Frozen trusted-base integrity (kernel + CodeSurface + contract + audit) =="
if [[ -f "$BASELINE" ]]; then
  if sha256sum -c "$BASELINE" --quiet 2>/dev/null; then
    echo "  OK: no frozen file changed since baseline."
  else
    echo "  DRIFT: a frozen file changed. Diff vs baseline and confirm the change is"
    echo "         ONLY a private->public exposure (no statement/proof/spec/audit/soundness"
    echo "         weakening, no new axiom). The contract spec, the audit guard, and the"
    echo "         four soundness theorems (SFormula.Deriv.sound, FamilyDeriv.sound,"
    echo "         ForallStabFamilyDeriv.sound, Formula.check_sound) MUST keep their exact"
    echo "         statements. Re-bless the baseline only after manual review."
    sha256sum -c "$BASELINE" 2>/dev/null | grep -v ': OK$'
    fail=1
  fi
else
  echo "  NOTE: no baseline at $BASELINE (first run). Recording current as baseline."
  sha256sum "${FROZEN[@]}" > "$BASELINE"
fi

echo "== [2] Banned tokens in prover-side Verify files =="
# Authoritative cheat check is the axiom gate in [4]; this is fast hygiene + early signal.
PROVER_FILES=$(find QStab/QHL/Verify -name '*.lean' \
  ! -name 'SurfaceDistanceContract.lean' ! -name 'SurfaceDistanceAudit.lean')
if grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom |@\[implemented_by|(^|[^a-zA-Z])unsafe |partial def|sorryAx' $PROVER_FILES 2>/dev/null \
     | grep -vE '^[^:]+:[0-9]+:\s*--' | grep -v '`'; then
  echo "  BANNED tokens present (above). Not 'perfect' yet."
  fail=1
else
  echo "  OK: no banned tokens in prover files."
fi

echo "== [3] Build the audit module =="
if lake build QStab.QHL.Verify.SurfaceDistanceAudit > "$LOG" 2>&1; then
  echo "  OK: build succeeded."
else
  echo "  BUILD FAILED (expected while incomplete/cheated). Key lines:"
  grep -iE 'CHEAT|forbidden|sorryAx|error:|✅|❌' "$LOG" | head -20
  fail=1
fi

echo "== [4] Axiom gate + statement pin (authoritative) =="
grep -iE "axiom-clean: .*audited_surface_distance|CHEAT DETECTED: 'QHL.*audited_surface_distance" \
  "$LOG" | head -5
if grep -q "axiom-clean: 'QHL.CodeLang.Surface.Verify.audited_surface_distance'" "$LOG"; then
  echo "  OK: audited_surface_distance is axiom-clean AND has the pinned statement (forall D, SurfaceDistanceSpec D)."
else
  echo "  NOT axiom-clean yet."
  fail=1
fi

echo
if [[ $fail -eq 0 ]]; then
  echo "RESULT: ✅ PERFECT — parametric (forall odd d) distance theorem proved, axiom-clean, trusted base intact."
else
  echo "RESULT: ❌ NOT YET — see sections above."
fi
exit $fail
