# Rothstein-Trager correctness reorganization

## Target module

`DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager` should be the random-access
entry point for the Rothstein-Trager and Lazard-Rioboo-Trager theory.

## Declarations to move

No declarations change namespace or meaning. Move only the module files:

- `DeepWiki.SymbolicIntegration.RtResultantCorrectness`
  to `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.RtResultantCorrectness`
- `DeepWiki.SymbolicIntegration.LazardRiobooTragerCorrectness`
  to `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LazardRiobooTragerCorrectness`
- `DeepWiki.SymbolicIntegration.CzichowskiNormalPosition`
  to `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.CzichowskiNormalPosition`

## Impact check

- `scripts/wiki rdeps DeepWiki.SymbolicIntegration.rtResultant --depth 1` shows RT resultant facts used by
  catalogs, `RtResultantCorrectness`, `LrtMonicLogs`, `CzichowskiNormalPosition`, and computable examples.
- `scripts/wiki rdeps DeepWiki.SymbolicIntegration.czichowskiR1 --depth 1` shows the Czichowski API is
  catalog-facing and self-contained after `CzichowskiNormalPosition`.
- Direct import rewrite set from `rg -l`:
  `DeepWiki/SymbolicIntegration.lean`, `LrtGeneralDerivation.lean`, `LrtMonicLogs.lean`,
  `RiobooCoprimalityLrt.lean`, and the four catalog/example files.

## Unify list

- The Rothstein-Trager aggregator imports `RtResultant`, `LrtSubresultant`, `LazardRiobooTragerCorrectness`,
  `CzichowskiNormalPosition`, and `RtResultantCorrectness`.
- Downstream files import the new module paths directly where they need a specific file.
- The old root-level modules are removed; declarations remain in `namespace DeepWiki.SymbolicIntegration`.

## Steps

1. `git mv` the three root files into `RationalIntegrationAlgorithms/RothsteinTrager/`.
2. Update imports in moved files, downstream theory files, source catalogs, and the topic root.
3. Gate the moved modules and affected catalogs with `scripts/check.sh`.
4. Run full `scripts/check.sh`.
5. Rebuild the wiki graph.
