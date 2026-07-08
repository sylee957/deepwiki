# Migration loop file sampling uses unavailable `shuf` on macOS

- **Date:** 2026-07-08
- **Tool/step:** migration-loop step 1 file mode
- **Expected:** the documented random-file command works in the repository's macOS environment.
- **Actual:** `find DeepWiki -name '*.lean' | grep -vE '/(MeasureTheory|NetworkCalculus|ReactiveSystems|RelationalDatabases|TimeSeries)/' | shuf | head -1` failed with `zsh:1: command not found: shuf`.
- **Why it's a limitation:** `shuf` is a GNU coreutils command and is not available by default on macOS.
- **Workaround used:** used an `awk` reservoir sample: `awk 'BEGIN{srand()} { if (rand() * NR < 1) line=$0 } END{ print line }'`.
- **Suggested fix:** update `docs/migration-loop.md` to use the portable `awk` command or document a macOS fallback.
- **Status:** open
