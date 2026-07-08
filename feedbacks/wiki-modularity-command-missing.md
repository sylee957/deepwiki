# `scripts/wiki modularity` is documented but unavailable

- **Date:** 2026-07-08
- **Tool/step:** `scripts/wiki modularity --prefix=DeepWiki.SymbolicIntegration.Computable.Algebraic --top=20`
- **Expected:** The migration-loop guidance says to use `scripts/wiki modularity` to inspect community partitions and directory fractures.
- **Actual:** The command failed with `unknown command: modularity`; the help output listed `recommend`, `search`, `show`, `deps`, `rdeps`, `path`, `context`, and `dot`, but not `modularity`.
- **Why it's a limitation:** The loop now points agents at a command that is not present in the current `wiki` CLI, so partition-mode scouting loses the detailed community breakdown.
- **Workaround used:** Use `scripts/wiki recommend --prefix=... --k=...` plus `wiki search`/`context`/`rdeps` and filesystem inspection to choose smaller safe reorgs.
- **Suggested fix:** Either restore/expose the `modularity` subcommand or update `docs/migration-loop.md` and repo guidance to describe the current `recommend`-based workflow.
- **Status:** open
