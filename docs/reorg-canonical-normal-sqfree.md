# Canonical representation squarefree-normal split

## Target module

`DeepWiki.SymbolicIntegration.CanonicalRepresentation.NormalSqfree`

## Declarations to move

- `IsNormalSqfree`
- `IsSplittingFactorizationGen`
- `IsNormal.isNormalSqfree`
- `IsSplittingFactorization.toGen`
- `isNormalSqfree_iff_isNormal_of_squarefree`

## Impact

These declarations are local structural predicates used by the general split-factor
correctness development in `CanonicalRepresentation.lean`. The public
`CanonicalRepresentation` module imports the new child module, preserving downstream
imports.

## Unify list

- Keep the squarefree-normal relaxation together.
- Leave split-factor recursion, squarefree split-factor formulas, canonical representation,
  and root characterization in the existing module for later staged splits.

## Steps

1. Add `CanonicalRepresentation/NormalSqfree.lean`.
2. Import it from `CanonicalRepresentation.lean`.
3. Remove the squarefree-normal section from the large file.
4. Gate the new module, then `CanonicalRepresentation`, then the full check.
5. Rebuild the wiki graph and commit.
