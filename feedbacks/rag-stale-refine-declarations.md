# Wiki graph misses current Refine declarations

- **Date:** 2026-07-14
- **Tool/step:** `scripts/wiki show`
- **Expected:** `scripts/wiki show DeepWiki.Refine.DependentCalculus.HasType.rename` and
  `scripts/wiki show DeepWiki.Refine.DependentCalculus.RawParametricity.translate_sort` locate the
  declarations that are present in the current Lean source.
- **Actual:** both commands exited successfully but reported `no declaration matching ...`.
- **Why it's a limitation:** the graph database predates the new dependent-calculus and raw
  parametricity declarations, so graph navigation silently omits the current proof API.
- **Workaround used:** inspected the current source with `rg` and direct file reads.
- **Suggested fix:** rebuild the graph after the Trocq modules land and make `show` distinguish a
  stale index from a genuinely absent declaration.
- **Status:** open
