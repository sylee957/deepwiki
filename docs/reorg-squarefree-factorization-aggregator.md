# Squarefree factorization aggregator split

## Theme

`DeepWiki.SymbolicIntegration.SquarefreeFactorization` currently contains the
abstract squarefree factorization loop and correctness proof while also sitting
beside the submodule `SquarefreeFactorization.Initialization`. As a newcomer,
the root path reads like an aggregator, but it is still a content module.

## Target Module

Move the content to:

- `DeepWiki.SymbolicIntegration.SquarefreeFactorization.Algorithm`

Keep the root module as an aggregator importing:

- `DeepWiki.SymbolicIntegration.SquarefreeFactorization.Initialization`
- `DeepWiki.SymbolicIntegration.SquarefreeFactorization.Algorithm`

## Decls To Move

All declarations currently in `SquarefreeFactorization.lean`, including:

- `gcd_squarefreePart_deflation`
- `squarefreeLoop`
- `squarefreeFactorization`
- `associated_div_iff`
- `squarefreeLoop_head_assoc`
- `squarefreeLoop_tail_assoc`
- `squarefreePart_deflation_natDegree_eq_zero_iff`
- `squarefreePart_deflation_natDegree_eq_zero_iff_maxmult`
- `sup_count_le_natDegree_primPart`
- `squarefreeFactorization_forall₂`

Private helper declarations move with the file.

## Impact

Existing callers import `DeepWiki.SymbolicIntegration.SquarefreeFactorization`,
so keeping the root aggregator preserves the public import path. No declaration
names or namespaces change.

Text import search shows consumers in rational integration, canonical
representation, the computable Yun bridge, source catalogs, and the topic
aggregator.

## Unify List

- No theorem unification in this pass.
- Separate module ownership only: initialization stays in `Initialization`,
  loop/correctness stays in `Algorithm`, root becomes an aggregator.

## Steps

1. `git mv SquarefreeFactorization.lean` to
   `SquarefreeFactorization/Algorithm.lean`.
2. Recreate `SquarefreeFactorization.lean` as an import-only aggregator.
3. Gate `DeepWiki.SymbolicIntegration.SquarefreeFactorization`.
4. Run full `scripts/check.sh`.
5. Rebuild `scripts/wiki build`.
6. Commit the split.
