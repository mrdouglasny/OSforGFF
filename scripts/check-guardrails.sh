#!/usr/bin/env bash
# Source-level guardrail check (build-independent), complementing the compile-time guard in
# OSforGFF/Guardrails.lean.
#
# The library's invariant is *absolute*, not relative to a baseline: the modules reachable from
# `OSforGFF.lean` declare no axioms, contain no `sorry`/`admit`, and use no escape hatches. This
# script scans the current tree for violations of that invariant directly, so — unlike a
# diff-against-a-tag check — it cannot silently pass by losing its reference point.
#
# Comments are stripped before scanning, so prose that merely *names* `axiom` or `sorry` (as
# OSforGFF/Guardrails.lean's own module docstring does) is not a false positive.
#
# `OSforGFF/Legacy/` is excluded: it is deliberately off the import graph, preserved for reference
# and never compiled by `lake build`. It is reported separately, for information only.
#
# `OSforGFF/OS/NonTrivial.lean` is also deliberately off the import graph but, unlike Legacy,
# is live mathematics: it is compiled here via `lake env lean` (needs a built library; skipped
# with a warning when `lake` is unavailable, or when GUARDRAIL_SKIP_OFFGRAPH=1).
#
#   exit 0  → clean
#   exit 2  → violation; intended to BLOCK when used as a CI step or a Stop hook.
#
# Usage:  scripts/check-guardrails.sh [REPO_ROOT]
#
#   GUARDRAIL_BASE=<rev>   also report which violations are *new* since <rev> (informational;
#                          the absolute scan above is always the gate).
set -uo pipefail

REPO="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"   # default: the repo this script sits in
cd "$REPO" 2>/dev/null || { echo "guardrails: repo not found: $REPO" >&2; exit 2; }

# The modules the guard covers: everything under OSforGFF/ plus the root module, minus the
# off-graph Legacy tree.
# (a `while read` loop rather than `mapfile`, which macOS's bash 3.2 lacks)
FILES=()
while IFS= read -r f; do
  FILES+=("$f")
done < <(find OSforGFF -name '*.lean' -not -path 'OSforGFF/Legacy/*' 2>/dev/null | sort)
FILES+=("OSforGFF.lean")
if [ "${#FILES[@]}" -le 1 ]; then
  echo "guardrails: no Lean sources found under $REPO/OSforGFF — wrong directory?" >&2
  exit 2
fi

# Emit `path:lineno:code` for every line, with Lean comments removed: `--` to end of line, and
# nestable `/- … -/` blocks (which subsume `/-- … -/` docstrings).
strip_comments() {
  awk '
    FNR == 1 { depth = 0 }
    {
      line = $0; out = ""; i = 1; n = length(line)
      while (i <= n) {
        two = substr(line, i, 2)
        if (depth > 0) {
          if (two == "-/") { depth--; i += 2; continue }
          if (two == "/-") { depth++; i += 2; continue }
          i++; continue
        }
        if (two == "/-") { depth++; i += 2; continue }
        if (two == "--") { break }
        out = out substr(line, i, 1); i++
      }
      print FILENAME ":" FNR ":" out
    }
  ' "$@"
}

CODE="$(strip_comments "${FILES[@]}")"

# An `axiom` declaration, at the start of a line (possibly indented, possibly after `private`
# or `protected`, possibly `@[...]`-attributed on a preceding line).
axioms=$(printf '%s\n' "$CODE" \
  | grep -E '^[^:]+:[0-9]+:[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)?axiom[[:space:]]' || true)

# Kernel escape hatches: trusted-code paths that let a false statement compile.
hatches=$(printf '%s\n' "$CODE" \
  | grep -E 'native_decide|(^|[^[:alnum:]_])unsafe([^[:alnum:]_]|$)|@\[implemented_by|@\[extern' || true)

# `sorry`/`admit`/`sorryAx` as code tokens.
sorries=$(printf '%s\n' "$CODE" \
  | grep -E '(^|[^[:alnum:]_])(sorry|sorryAx|admit)([^[:alnum:]_]|$)' || true)

fail=0
report() { # report <label> <findings>
  local label="$1" findings="$2"
  [ -z "$findings" ] && return 0
  echo "✗ BLOCK: $label" >&2
  printf '%s\n' "$findings" | sed 's/^/    /' >&2
  fail=1
}

report "axiom declaration(s) in the build graph (the library declares none):" "$axioms"
report "kernel escape hatch (native_decide/unsafe/implemented_by/extern):" "$hatches"
report "sorry/admit in the build graph:" "$sorries"

# Optional: attribute the violations to a range, for a reviewer looking at a specific change.
BASE="${GUARDRAIL_BASE:-}"
if [ "$fail" -ne 0 ] && [ -n "$BASE" ]; then
  if git rev-parse -q --verify "$BASE^{commit}" >/dev/null 2>&1; then
    echo "── introduced since $BASE (added lines only) ──" >&2
    git diff "$BASE" -- OSforGFF OSforGFF.lean ':(exclude)OSforGFF/Legacy/*' 2>/dev/null \
      | grep -E '^\+' | grep -Ev '^\+\+\+' \
      | grep -E '^\+[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)?axiom[[:space:]]|native_decide|@\[implemented_by|@\[extern|(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)' \
      | sed 's/^/    /' >&2 || true
  else
    echo "guardrails: GUARDRAIL_BASE='$BASE' is not a commit; skipping the attribution report" >&2
  fi
fi

if [ "$fail" -ne 0 ]; then
  echo "✗ guardrail BLOCK — resolve before continuing." >&2
  exit 2
fi

legacy=$(grep -rlE '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)|^[[:space:]]*axiom[[:space:]]' \
  --include='*.lean' OSforGFF/Legacy 2>/dev/null || true)
if [ -n "$legacy" ]; then
  echo "ℹ note: off-graph OSforGFF/Legacy/ mentions sorry/axiom (not compiled, not a violation):"
  printf '%s\n' "$legacy" | sed 's/^/    /'
fi

# Off-graph verification: OS/NonTrivial.lean is deliberately not imported by the root, so
# `lake build` never compiles it. The source scan above already covers it (it is under
# OSforGFF/, outside Legacy/); this step additionally checks that its proofs still compile.
if [ -n "${GUARDRAIL_SKIP_OFFGRAPH:-}" ]; then
  echo "ℹ note: off-graph compile of OS/NonTrivial.lean skipped (GUARDRAIL_SKIP_OFFGRAPH set)"
elif ! command -v lake >/dev/null 2>&1; then
  echo "⚠ warning: 'lake' not found — off-graph OS/NonTrivial.lean NOT compiled" >&2
else
  if ! lake env lean OSforGFF/OS/NonTrivial.lean; then
    echo "✗ BLOCK: off-graph OSforGFF/OS/NonTrivial.lean fails to compile" >&2
    exit 2
  fi
  echo "✓ off-graph OS/NonTrivial.lean compiles"
fi

echo "✓ guardrails: clean — ${#FILES[@]} modules, no axiom/sorry/escape-hatch in the build graph"
exit 0
