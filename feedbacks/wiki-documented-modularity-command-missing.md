# Repository guidance advertises a missing `wiki modularity` command

- **Date:** 2026-07-14
- **Tool/step:** `scripts/wiki modularity`
- **Expected:** The repository guidance lists `modularity` as a first-class structural audit command.
- **Actual:** `scripts/wiki modularity` prints `unknown command: modularity`; its help lists no such subcommand.
- **Why it's a limitation:** The documented refactoring workflow cannot be followed with the checked-in CLI.
- **Workaround used:** Used `wiki show`, source inspection, and exact dependency searches for this audit.
- **Suggested fix:** Restore the subcommand or remove/update the stale guidance and point to its replacement.
- **Status:** open
