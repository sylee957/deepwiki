# `scripts/wiki build` fails when the graph database is locked

- **Date:** 2026-07-11
- **Tool/step:** `scripts/wiki build`
- **Expected:** Refresh `.wiki/graph.db` after a green library refactor.
- **Actual:** The command loaded the environment, then terminated with `database is locked (error code: 5)`.
- **Why it's a limitation:** A concurrent or stale SQLite connection prevents graph refresh, while later query commands can still return plausibly current-looking results from the old database.
- **Workaround used:** Confirm reverse dependencies against current source with `rg`, treat `scripts/wiki rdeps` as advisory until a later refresh succeeds, and retry the build before deletion decisions.
- **Suggested fix:** Configure a busy timeout or transactional retry for graph replacement, and make query commands report the graph build revision.
- **Status:** open
