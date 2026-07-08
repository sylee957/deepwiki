# Laurent base layer reorganization

## Target modules

- `DeepWiki.SymbolicIntegration.LaurentCoefficients.Cofactors`
- `DeepWiki.SymbolicIntegration.LaurentCoefficients.Numerator`
- `DeepWiki.SymbolicIntegration.LaurentCoefficients.Base` as the stable aggregator

## Declarations to move

`Cofactors` keeps the denominator and Bezout data:

- `laurentE`
- `bezoutE`
- `bezoutDeriv`
- `bezoutE_mul_laurentE_modByMonic`
- `bezoutDeriv_mul_derivative_modByMonic`

`Numerator` keeps the differential-polynomial numerator recursion:

- `laurentNumStep`
- `laurentNum`
- `laurentNum_zero`
- `laurentNum_succ`
- `laurentNum_cleared_step`

## `wiki rdeps` impact

- `laurentE`, `bezoutE`, and `bezoutDeriv` feed the engine output definitions and root-evaluation congruences.
- `laurentNum` feeds the fraction invariant, root invariant, engine output, and Taylor-coefficient bridge.
- Keeping `LaurentCoefficients.Base` as an aggregator preserves current downstream import paths.

## Unify list

- The cofactor layer should be readable independently as the extended-Euclidean input data.
- The numerator layer should be readable independently as the recursive differential-polynomial engine.
- No declarations are redundant; this is a pure module split along the concept boundary.

## Steps

1. Move the existing `Base.lean` body to `Cofactors.lean` and trim it to the cofactor declarations.
2. Add `Numerator.lean` with the numerator recursion declarations unchanged.
3. Recreate `Base.lean` as an aggregator importing `Cofactors` and `Numerator`.
4. Gate `Cofactors`, `Numerator`, `Base`, `Engine`, and downstream Laurent modules.
5. Run full `scripts/check.sh`, rebuild the wiki graph, and commit.
