# `wiki rdeps` silently misses newly added declarations

- **Date:** 2026-07-11
- **Tool/step:** `scripts/wiki rdeps`
- **Expected:** `scripts/wiki rdeps DeepWiki.SymbolicIntegration.CRischLevel --depth 3` resolves the declaration built by the current library.
- **Actual:** It returned `no declaration matching` for `CRischLevel`, `LawfulCRischLevel`, and `oneLevelRisch` even though all three compile.
- **Why it's a limitation:** The graph database can be stale relative to recent library commits, but the query does not identify staleness.
- **Workaround used:** Run `scripts/wiki build` before the deletion or signature-change audit, then repeat `rdeps`.
- **Suggested fix:** Store and compare the indexed source or environment revision and warn when queries run against a stale graph.
- **Status:** open

## Follow-up: 2026-07-12

- **Tool/step:** `scripts/wiki rdeps` during the presentation-tower retirement audit.
- **Expected:** newly compiled `LayeredTranscendentalStage.asPresentationTowerCoefficientStage`
  and `LayeredTranscendentalLevel.asTowerCoefficientStage` resolve for caller audits.
- **Actual:** both qualified queries returned `no declaration matching`, while their definitions
  are present in `Engine/Tower/Transcendental.lean` and compile through the full library.
- **Workaround used:** treat source imports and `rg` as authoritative for this audit; rebuild the
  graph before the next deletion decision.
