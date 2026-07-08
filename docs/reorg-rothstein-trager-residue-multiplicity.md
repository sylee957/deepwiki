# Rothstein-Trager residue multiplicity reorganization

## Target module

Move the RT resultant residue/root-multiplicity bridge into
`DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager`.

## Declarations to move

No declarations change namespace or meaning. Move only the module file:

- `DeepWiki.SymbolicIntegration.ResidueMultiplicity`
  to `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.ResidueMultiplicity`

## Impact check

- `scripts/wiki rdeps DeepWiki.SymbolicIntegration.rootMultiplicity_rtResultant_eq_natDegree_gcd --depth 2`
  shows the bridge is used by LRT correctness, monic LRT log regularity, and source catalog entries.
- `Residues.lean` remains root-level because it provides the general simple-residue and gcd-root API used
  beyond the RT resultant.

## Unify list

- The Rothstein-Trager aggregator imports `ResidueMultiplicity` before the correctness/Czichowski modules.
- Downstream imports of the old root path are rewritten to the new module path.

## Steps

1. `git mv` `ResidueMultiplicity.lean` into `RationalIntegrationAlgorithms/RothsteinTrager/`.
2. Update direct import paths.
3. Gate `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager` and affected catalogs.
4. Run full `scripts/check.sh`.
5. Rebuild the wiki graph.
