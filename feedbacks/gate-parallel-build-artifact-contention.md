# Parallel focused gates can corrupt transient Lake setup files

- **Date:** 2026-07-08
- **Tool/step:** scripts/check.sh focused targets run concurrently
- **Expected:** Two focused `scripts/check.sh` invocations should either serialize safely or fail with an ordinary Lean/build error.
- **Actual:** Running `scripts/check.sh DeepWiki.SymbolicIntegration.DifferentialAlgebraFacts` in parallel with `scripts/check.sh Sources.Doi_10_1007_b138171.Chapter3` produced `failed to load header ... Closure.setup.json: offset 0: unexpected end of input`; the other build then rebuilt the same module successfully.
- **Why it's a limitation:** Concurrent Lake builds can race on generated `.setup.json`/IR artifacts, yielding a spurious gate failure unrelated to the edited Lean code.
- **Workaround used:** Let the parallel build finish, then rerun the failed focused target sequentially.
- **Suggested fix:** Document that `scripts/check.sh` invocations should not be parallelized, or make the script acquire a build lock.
- **Status:** open
