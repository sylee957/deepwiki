# `wiki rdeps` misses cross-file uses inside anonymous examples

- **Date:** 2026-07-11
- **Tool/step:** `scripts/wiki rdeps DeepWiki.SymbolicIntegration.hreducedLrt_of_genuineAll --depth 2`
- **Expected:** A cross-file reference that prevents privatizing or deleting the theorem should appear as a dependent.
- **Actual:** The command reported zero dependents, while `RischTowerLrtGrounding.lean` contains two calls to the theorem inside a `noncomputable example`.
- **Why it's a limitation:** Anonymous examples do not become named declaration nodes, so their source-level dependencies are absent from the declaration-use graph even though they are compile dependencies relevant to visibility and deletion audits.
- **Workaround used:** Pair `scripts/wiki rdeps` with `rg` over Lean sources before applying `private` or deleting a declaration.
- **Suggested fix:** Add a source-reference fallback for anonymous commands, or make `rdeps` warn that anonymous-example uses are outside its coverage.
- **Status:** open
