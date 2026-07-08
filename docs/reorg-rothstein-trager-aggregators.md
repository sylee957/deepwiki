# Rothstein-Trager Aggregators Reorg

## Target module

`DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager`

## Theme

The Rothstein-Trager root aggregator currently imports every leaf directly. For
random access, it should expose the main conceptual stages: resultant primitives,
residue theory, Lazard-Rioboo-Trager subresultant/correctness, general-derivation
bridges, and Czichowski normal position.

## Decls to move

None. This is an aggregator-only reorganization. All declaration meanings and
declaration modules remain unchanged.

## Impact

- Direct leaf imports by consumers remain valid.
- The root `RothsteinTrager` module remains the umbrella import.
- No executable/native-decision path changes.

## Unify list

- `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.Resultant`
  - `RtResultant`
  - `RtResultantCorrectness`
- `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.Residue`
  - `ResidueMultiplicity`
  - `LogResidueTower`
- `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.Lrt`
  - `LrtSubresultant`
  - `LazardRiobooTragerCorrectness`
  - `LrtGeneralDerivation`
- Keep `CzichowskiNormalPosition` as the normal-position geometry leaf.

## Steps

1. Add the three conceptual aggregator modules.
2. Replace the flat `RothsteinTrager.lean` import wall with those aggregators plus
   `CzichowskiNormalPosition`.
3. Gate `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager`,
   then the full `scripts/check.sh`.
4. Rebuild the wiki graph and commit the pure aggregator split.
