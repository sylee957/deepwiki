#!/usr/bin/env bash
# Proof-result gate for the agent loop.
#
# Runs the full `lake build` correctness gate over the Book library and
# reports a single verdict. Mathlib is cached, so this only ever recompiles
# changed Book/*.lean chapters.
#
# Timing (warm filesystem cache, this machine):
#   - no-op (nothing changed):            ~2.4s  (lake manifest + olean stat floor)
#   - one chapter actually recompiled:    ~2.4s + chapter elab (0-3s)
#
# Exit codes:
#   0  build succeeded, no errors / warnings / sorry
#   1  build failed, OR build "succeeded" but emitted a warning or `sorry`
#      (CLAUDE.md requires the build to be warning-free and sorry-free)
#
# Usage:
#   scripts/check.sh            # full gate over `Book`
#   scripts/check.sh Book.Limits   # gate a single chapter (faster feedback)

set -u
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")/.." || exit 1

TARGET="${1:-Book}"

# Capture combined output so we can scan it; tee nothing to keep the loop quiet.
out="$(lake build "$TARGET" 2>&1)"
status=$?

echo "$out"

if [ "$status" -ne 0 ]; then
  echo "GATE: FAIL (lake build exited $status)"
  exit 1
fi

# `lake build` can exit 0 while Lean printed warnings/sorries to the log.
if echo "$out" | grep -qiE "declaration uses 'sorry'|error:|warning:"; then
  echo "GATE: FAIL (warning/error/sorry in build output)"
  exit 1
fi

echo "GATE: PASS"
exit 0
