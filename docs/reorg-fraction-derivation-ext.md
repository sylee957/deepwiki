# Fraction-field derivation extension reorg

## Target module

Consolidate fraction-field derivation extensionality and uniqueness in
`DeepWiki.SymbolicIntegration.Core.Differential.DerivationExt`.

## Declarations to move

Move from `DeepWiki.SymbolicIntegration.DifferentialExtensions`:

- `unique_derivation_fractionRing`
- `existsUnique_derivation_fractionRing`

## Impact

`wiki rdeps` before the move:

- `unique_derivation_fractionRing`: used by `existsUnique_derivation_fractionRing` and the source catalog.
- `existsUnique_derivation_fractionRing`: used by the source catalog.

Existing import sites remain valid because `DifferentialExtensions` imports `DerivationExt`.

## Steps

1. Move the two fraction-field uniqueness wrappers into `Core.Differential.DerivationExt`.
2. Remove the old `FractionField` section from `DifferentialExtensions`.
3. Gate the affected modules and full build, rebuild the graph, then commit.
