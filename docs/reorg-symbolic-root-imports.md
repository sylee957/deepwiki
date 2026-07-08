# SymbolicIntegration Root Import Cleanup

## Target modules

- `DeepWiki.SymbolicIntegration`
- `DeepWiki.SymbolicIntegration.GroebnerBasis`

## Theme

The topic root and the public Groebner file should use semantic aggregators instead
of hand-listing already-covered leaf modules. This keeps random access oriented
around conceptual entry points rather than dependency history.

## Decls to move

None. This is import-only.

## Impact

- `DeepWiki.SymbolicIntegration` remains the topic umbrella.
- `DeepWiki.SymbolicIntegration.GroebnerBasis` remains the public Groebner-facing
  file, but imports the core Groebner support through its aggregator.
- No executable/native-decision path changes.

## Unify list

- Drop duplicate topic-root imports already covered by:
  - `AlgebraicCompleteness`
  - `RationalIntegrationAlgorithms`
- Replace the flat core Groebner leaf list in `GroebnerBasis.lean` with
  `Core.Polynomial.Groebner`.

## Steps

1. Remove duplicate leaf imports from `DeepWiki/SymbolicIntegration.lean`.
2. Replace `GroebnerBasis.lean`'s Groebner support import wall with the new
   `DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner` entry point.
3. Gate `DeepWiki.SymbolicIntegration.GroebnerBasis`, then the topic root and full gate.
4. Rebuild the wiki graph and commit.
