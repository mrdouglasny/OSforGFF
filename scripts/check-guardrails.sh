#!/usr/bin/env bash
# Source-level guardrail check (build-independent), complementing the compile-time guard in
# OSforGFF/Guardrails.lean. Two modes:
#   - diff mode (baseline tag `pre-unfreeze-baseline` present): flags anything introduced since
#     the baseline tag.
#   - scan mode (tag absent, e.g. a fresh clone fetched without tags): scans the entire
#     OSforGFF/ source tree for the same patterns. Equivalent here — the baseline declares
#     none of them — and keeps the check functional in every clone.
# Runnable manually or via the Stop hook.
#
#   exit 0  → clean (or warnings only)
#   exit 2  → hard violation (new axiom / escape hatch); intended to BLOCK when used as a Stop hook.
set -uo pipefail

REPO="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"   # default: the repo root
cd "$REPO" 2>/dev/null || { echo "guardrails: repo not found: $REPO"; exit 0; }
BASE="pre-unfreeze-baseline"

# hits PATTERN — lines matching PATTERN, excluding OSforGFF/Guardrails.lean (which legitimately
# mentions `axiom`/`sorry`). Diff mode emits added lines vs the baseline (stripped of the leading
# `+`); scan mode emits file:line: matches over the whole tree.
if git rev-parse -q --verify "refs/tags/$BASE" >/dev/null 2>&1; then
  MODE="diff vs baseline tag '$BASE'"
  hits() {
    git diff "$BASE" -- OSforGFF ':(exclude)OSforGFF/Guardrails.lean' 2>/dev/null \
      | grep -E '^\+' | grep -Ev '^\+\+\+' | sed 's/^+//' | grep -E "$1" || true
  }
else
  MODE="full-tree scan (baseline tag '$BASE' absent)"
  hits() {
    grep -rnE --include='*.lean' --exclude='Guardrails.lean' "$1" OSforGFF 2>/dev/null || true
  }
fi
echo "guardrails: mode = $MODE"

fail=0
newax=$(hits '^[[:space:]]*axiom[[:space:]]')
hatch=$(hits 'native_decide|[^[:alnum:]_]unsafe[^[:alnum:]_]|@\[implemented_by|@\[extern')
sorries=$(hits '(:=|[^[:alnum:]_]by[^[:alnum:]_]|;)[[:space:]]*(sorry|admit)([^[:alnum:]_]|$)|sorryAx|^[[:space:]]*(sorry|admit)[[:space:]]*$')

if [ -n "$newax" ];  then echo "✗ BLOCK: axiom(s) in source (the library declares none):" >&2; echo "$newax" >&2; fail=1; fi
if [ -n "$hatch" ];  then echo "✗ BLOCK: escape hatch introduced (native_decide/unsafe/implemented_by/extern):" >&2; echo "$hatch" >&2; fail=1; fi
if [ -n "$sorries" ]; then echo "⚠ WARN: sorry/admit in source — the build's #print axioms guard is the hard gate:"; echo "$sorries"; fi

if [ "$fail" -ne 0 ]; then
  echo "✗ guardrail BLOCK — resolve before continuing." >&2
  exit 2
fi
[ -z "$sorries" ] && echo "✓ guardrails: clean (no axiom/sorry/escape-hatch)"
exit 0
