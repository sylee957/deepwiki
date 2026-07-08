# Normal/special transport reorganization

## Target module

Create `DeepWiki.SymbolicIntegration.Core.Differential.NormalSpecial.Transport` for unit/associate
transport and splitting-factorization declarations, leaving
`DeepWiki.SymbolicIntegration.Core.Differential.NormalSpecial` focused on the core normal/special
definitions and closure/gcd API.

## Declarations to move

- `isUnit_of_isNormal_of_isSpecial`
- `isNormal_of_isUnit`
- `isNormal_and_isSpecial_iff_isUnit`
- `IsSpecial.unit_mul_iff`
- `IsNormal.unit_mul_iff`
- `IsSpecial.of_associated`
- `IsNormal.of_associated`
- `IsSplittingFactorization`
- `IsSpecial.splittingFactorization`
- `IsNormal.splittingFactorization`

## Impact

`scripts/wiki rdeps` shows the moved declarations are used by:

- `Sources.Doi_10_1007_b138171.Chapter3`
- `CanonicalRepresentation.{SplitFactorCorrect,SplitSquarefreeFactor,RootCharacterization,SplitFactor,NormalSqfree}`
- `Computable.SplitFactorWfCorrect`
- `MonomialConstants.Scalar`

The old `NormalSpecial` module will import the new leaf for compatibility, so existing downstream imports
remain valid.

## Unify list

- Keep names, statements, and proofs unchanged.
- Separate core predicate algebra from unit/associate/splitting transport.
- Do not touch executable definitions or native-decide paths.

## Steps

1. Add `NormalSpecial/Transport.lean` with the transport and splitting declarations.
2. Import the new leaf from `NormalSpecial.lean` and remove duplicate declarations there.
3. Gate the new leaf, `NormalSpecial`, direct consumers, and full `scripts/check.sh`.
4. Rebuild the wiki graph and commit.
