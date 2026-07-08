# Migration loop random sample command assumes `shuf`

- **Date:** 2026-07-08
- **Tool/step:** migration-loop step 1 file-mode sampling
- **Expected:** The documented random-file command should work in this checkout environment.
- **Actual:** `find DeepWiki -name '*.lean' | grep -vE '/(MeasureTheory|NetworkCalculus|ReactiveSystems|RelationalDatabases|TimeSeries)/' | shuf | head -1` failed with `zsh:1: command not found: shuf`.
- **Why it's a limitation:** macOS does not provide GNU `shuf` by default, so the documented loop is not portable for this workspace.
- **Workaround used:** Use a small Ruby sampler over the same filtered file list.
- **Suggested fix:** Document a portable fallback such as `ruby -e 'puts STDIN.readlines.sample'`.
- **Status:** open
