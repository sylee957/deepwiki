# `scripts/wiki rdeps` misses a namespaced definition

- **Date:** 2026-07-12
- **Tool/step:** `scripts/wiki rdeps DensePoly.cIntegrateGFullWf --depth 3`
- **Expected:** the tool resolves the definition that `scripts/wiki search cIntegrateGFullWf` reports as `DeepWiki.SymbolicIntegration.DensePoly.cIntegrateGFullWf`.
- **Actual:** it reports `no declaration matching 'DensePoly.cIntegrateGFullWf'`; the fully qualified spelling also produced no result after `scripts/wiki build`.
- **Why it's a limitation:** a normal declaration search finds the definition, but reverse-dependency lookup cannot resolve the same namespace-qualified name.
- **Workaround used:** audited direct imports and call sites with `rg` before the retirement.
- **Suggested fix:** make `rdeps` use the same short-name resolution as `show` and `search`.
- **Status:** open
