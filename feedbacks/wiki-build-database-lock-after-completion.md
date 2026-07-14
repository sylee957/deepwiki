# Graph rebuild can leave a transient SQLite lock

- **Date:** 2026-07-14
- **Tool/step:** `scripts/wiki build`, immediately followed by `scripts/wiki show`
- **Expected:** A completed rebuild should make the refreshed graph immediately queryable.
- **Actual:** The rebuild invocation returned without output, the first follow-up rebuild failed with
  `uncaught exception: database is locked (error code: 5)`, and the graph became queryable shortly
  afterward with the new declarations present.
- **Why it's a limitation:** Automation cannot distinguish a completed silent rebuild from a
  still-finalizing database write, so an immediate structural query can fail spuriously.
- **Workaround used:** Waited for the database timestamp to advance, then retried the read-only
  searches; all new declarations were present.
- **Suggested fix:** Hold the wrapper lock through SQLite finalization and emit a completion line
  only after a read-only probe succeeds.
- **Status:** open
