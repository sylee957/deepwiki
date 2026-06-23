#!/usr/bin/env bash
# PreToolUse(Bash) hook: make git worktrees reuse the main repo's built
# `.lake` dependency artifacts (Mathlib's ~8k oleans) instead of rebuilding
# them from scratch.
#
# A fresh `git worktree add` checkout has an empty `.lake`, so `lake build`
# re-resolves and recompiles the entire Mathlib closure (very slow, ~8.5G).
# The fix: symlink the worktree's `.lake/packages` to the main repo's, so the
# worktree reuses all dependency oleans and only recompiles the local `Book`
# target. Each worktree keeps its own `.lake/build` (its `Book/*.lean` differs).
#
# Idempotent and fast: it only acts when run inside a worktree whose link is
# not yet set up, and exits 0 otherwise. Never blocks the tool call.

set -u

# The canonical main checkout. CLAUDE_PROJECT_DIR is set by the harness to the
# project root; fall back to this script's grandparent (.claude/<script>).
MAIN="${CLAUDE_PROJECT_DIR:-}"
if [ -z "$MAIN" ]; then
  MAIN="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
fi

# Resolve the main repo's real working tree (in case PROJECT_DIR is a worktree
# itself, walk to the common dir's parent). We only need its `.lake`.
MAIN_LAKE="$MAIN/.lake"
[ -d "$MAIN_LAKE/packages" ] || exit 0   # nothing built to share yet

# Operate on the directory the tool call runs in.
CWD="$(pwd -P)"

# Only act inside a worktree checkout (under .claude/worktrees/...).
case "$CWD" in
  */.claude/worktrees/*) ;;
  *) exit 0 ;;
esac

# Find the worktree root: the nearest ancestor containing a `lakefile.toml`.
WT="$CWD"
while [ "$WT" != "/" ] && [ ! -f "$WT/lakefile.toml" ]; do
  WT="$(dirname "$WT")"
done
[ -f "$WT/lakefile.toml" ] || exit 0

# Don't link a worktree to itself (e.g. if MAIN somehow equals WT).
[ "$WT" = "$MAIN" ] && exit 0

WT_LAKE="$WT/.lake"

# If packages is already the shared symlink, we're done (fast path).
if [ -L "$WT_LAKE/packages" ] && \
   [ "$(readlink "$WT_LAKE/packages")" = "$MAIN_LAKE/packages" ]; then
  exit 0
fi

mkdir -p "$WT_LAKE"

# Replace any real/empty packages dir with a symlink to the main repo's.
# (A fresh worktree either has no .lake/packages or a stale partial one.)
if [ -e "$WT_LAKE/packages" ] && [ ! -L "$WT_LAKE/packages" ]; then
  rm -rf "$WT_LAKE/packages"
fi
ln -sfn "$MAIN_LAKE/packages" "$WT_LAKE/packages"

# Share the resolved config (toolchain/manifest) too, so lake doesn't re-fetch.
if [ -d "$MAIN_LAKE/config" ] && [ ! -e "$WT_LAKE/config" ]; then
  ln -sfn "$MAIN_LAKE/config" "$WT_LAKE/config"
fi

# Warm the local `.lake/build` once by COPYING (not symlinking) the main repo's
# oleans. The DeepWiki library here is ~1500 modules, so a cold rebuild from an
# empty build dir is many minutes; the one-time ~3G copy makes the worktree's
# first `lake build`/gate ~seconds (lake accepts the copied oleans despite the
# different source path). Each worktree keeps its OWN writable build (its sources
# differ), so we copy rather than share. Idempotent: skip once build exists.
if [ ! -d "$WT_LAKE/build" ] && [ -d "$MAIN_LAKE/build" ]; then
  cp -a "$MAIN_LAKE/build" "$WT_LAKE/build"
fi

exit 0
