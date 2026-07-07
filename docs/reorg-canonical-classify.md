# Canonical representation classifier split

## Target module

`DeepWiki.SymbolicIntegration.CanonicalRepresentation.Classify`

## Declarations to move

- `IsSimple`, `IsReduced`
- `isSimple_iff_isNormal_denom`, `isReduced_iff_isSpecial_denom`
- `isSimple_algebraMap`, `isReduced_algebraMap`
- `isReduced_of_dvd_implicitDeriv`, `isSimple_of_isCoprime_implicitDeriv`
- `isSimple_zero`, `isReduced_zero`

## Impact

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.IsSimple --depth 2` and
`scripts/wiki rdeps DeepWiki.SymbolicIntegration.IsReduced --depth 2` show only
the local classifier API and the Chapter 3 source aliases. The public
`CanonicalRepresentation` module will import the new child module, preserving
downstream imports.

## Unify list

- Move only the RatFunc classification predicates and their small intro/base
  lemmas.
- Leave split-factor, squarefree, canonical representation, and root
  characterization facts in the existing module for later splits.

## Steps

1. Add `CanonicalRepresentation/Classify.lean`.
2. Import it from `CanonicalRepresentation.lean`.
3. Remove the classifier section from the large file.
4. Gate the new module, then `CanonicalRepresentation`, then the full check.
5. Rebuild the wiki graph and commit.
