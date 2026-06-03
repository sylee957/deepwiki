#!/usr/bin/env bash
# Render the Verso book to _out/html-multi without ever disturbing a
# running server.
#
# The renderer creates "html-multi 2" duplicates only when it writes
# *into* a directory something else holds (an http.server, or a shell
# whose cwd is inside it). We sidestep that entirely: render to a
# staging dir, then atomically swap it into place with `mv`. A live
# server keeps serving the old files (held by inode) until its next
# request, then picks up the new ones — nothing is killed.
#
# Usage:
#   ./render.sh            render once and swap in
#   ./render.sh --watch    re-render on changes to Book/, Book.lean, Main.lean
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"

OUT=_out/html-multi
STAGE=_out/.staging

render_once() {
  rm -rf "$STAGE"
  # Render into the staging dir (lays out as $STAGE/html-multi/).
  if ! lake exe generate-book --output "$STAGE"; then
    echo "ERROR: render failed; live output left untouched." >&2
    rm -rf "$STAGE"
    return 1
  fi
  if [ ! -f "$STAGE/html-multi/index.html" ]; then
    echo "ERROR: staged render has no html-multi/index.html." >&2
    rm -rf "$STAGE"
    return 1
  fi
  # Atomic-ish swap: drop the old tree, move the new one in. Both live
  # under _out (same filesystem), so the final mv is a rename.
  rm -rf "$OUT"
  # Sweep any stray "html-multi 2"/"html-multi 3" left by past bad runs.
  find _out -maxdepth 1 -name 'html-multi [0-9]*' -exec rm -rf {} + \
    2>/dev/null || true
  mkdir -p _out
  mv "$STAGE/html-multi" "$OUT"
  rm -rf "$STAGE"
  echo "OK: $OUT updated (no server restart needed)."
}

# Fingerprint of the source files, to detect changes in --watch mode.
sources_hash() {
  { find Book -type f -name '*.lean' -print0 2>/dev/null;
    printf '%s\0' Book.lean Main.lean; } \
    | xargs -0 stat -f '%m %N' 2>/dev/null | sort | shasum | cut -d' ' -f1
}

if [ "${1:-}" = "--watch" ]; then
  echo "Watching Book/, Book.lean, Main.lean — Ctrl-C to stop."
  render_once || true
  if command -v fswatch >/dev/null 2>&1; then
    fswatch -o Book Book.lean Main.lean | while read -r _; do
      echo "change detected; re-rendering…"; render_once || true
    done
  else
    last=$(sources_hash)
    while true; do
      sleep 2
      now=$(sources_hash)
      if [ "$now" != "$last" ]; then
        last=$now
        echo "change detected; re-rendering…"; render_once || true
      fi
    done
  fi
else
  render_once
fi
