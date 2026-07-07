# Canonical representation split-factor base split

## Target module

`DeepWiki.SymbolicIntegration.CanonicalRepresentation.SplitFactor`

## Declarations to move

- `splitFactorStep`
- `splitFactorAux`
- `splitFactor`
- `IsSplitFactorStep`
- `splitFactorAux_isSplittingFactorization`
- `splitFactor_isSplittingFactorization`

## Impact

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.splitFactor --depth 2` reports
local use by canonical representation correctness plus Chapter 3 source aliases.

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.IsSplitFactorStep --depth 2`
reports local fully-split and abstract correctness proofs plus the Chapter 3 source
alias.

The parent `CanonicalRepresentation` module imports this child, so existing
downstream imports remain valid.

## Unify list

- Keep the abstract algorithm and its assumed-step correctness theorem together.
- Leave fully-split formulas, general prime-factor formulas, concrete step proof,
  canonical representation, and root characterization in the parent for later
  staged splits.

## Steps

1. Add `CanonicalRepresentation/SplitFactor.lean`.
2. Import it from `CanonicalRepresentation.lean`.
3. Remove the split-factor base section from the parent.
4. Gate the child, parent, and full build.
5. Rebuild the wiki graph and commit.
