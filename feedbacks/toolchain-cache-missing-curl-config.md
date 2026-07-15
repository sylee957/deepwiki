# Mathlib cache download fails after completing all transfers

- **Date:** 2026-07-15
- **Tool/step:** `lake exe cache get` during the Lean/Mathlib v4.32 migration
- **Expected:** The cache command downloads and decompresses the requested artifacts, then exits successfully.
- **Actual:** After reporting `Downloaded: 5251 file(s) ... 100%`, it exited with `uncaught exception: no such file or directory ... /Users/sangyub/.cache/mathlib/curl.cfg`.
- **Why it's a limitation:** The cache client assumes its generated curl configuration still exists at finalization time, so a completed transfer can be reported as a failure.
- **Workaround used:** Continue with the artifacts already decompressed and run the build; retry cache retrieval only if required objects are missing.
- **Suggested fix:** Keep the curl configuration alive for the full cache process or make final cleanup tolerate an already-missing temporary config.
- **Status:** open
