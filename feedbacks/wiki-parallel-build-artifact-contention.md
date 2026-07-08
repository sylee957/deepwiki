# Parallel `scripts/wiki` calls can race on WikiRAG build artifacts

- **Date:** 2026-07-08
- **Tool/step:** `scripts/wiki rdeps`
- **Expected:** Independent read-only wiki queries can run safely in parallel.
- **Actual:** Running two `scripts/wiki rdeps` commands concurrently caused one Lake build of `WikiRAG.Main` to fail with `failed to load header ... WikiRAG/Main.setup.json: offset 0: unexpected end of input`, while the other query succeeded.
- **Why it's a limitation:** `scripts/wiki` may build the `wiki` executable before querying; concurrent Lake builds can race on generated `.setup.json`/IR artifacts, like the known `scripts/check.sh` parallel-build issue.
- **Workaround used:** Rerun the failed wiki query sequentially after the other query exits.
- **Suggested fix:** Document that `scripts/wiki` commands which may trigger a build should also be run sequentially, or make `scripts/wiki` serialize its own build step.
- **Status:** open
