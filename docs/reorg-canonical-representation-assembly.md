# Canonical representation assembly reorg

## Target module

Create `DeepWiki.SymbolicIntegration.CanonicalRepresentation.Assembly`.

`DeepWiki.SymbolicIntegration.CanonicalRepresentation` should become the directory aggregator,
while `Assembly` owns the Bézout split and final `canonicalRepresentation` construction.

## Decls to move

- `extendedEuclideanSplit`
- `extendedEuclideanSplit_spec`
- `extendedEuclideanSplit_degree_lt`
- `bezoutOne`
- `bezoutOne_spec`
- `canonicalRepresentation`
- `canonicalRepresentation_add_eq`
- `canonicalRepresentation_sum_eq`

## `wiki rdeps` impact

- `extendedEuclideanSplit` is used by its local specs and by `canonicalRepresentation`.
- `canonicalRepresentation` is used by the Chapter 3 source catalog aliases and
  `canonicalRepresentation_sum_eq`.
- `canonicalRepresentation_sum_eq` is used by the Chapter 3 source catalog alias.

Direct text imports of the root module are:

- `DeepWiki/SymbolicIntegration.lean`
- `DeepWiki/SymbolicIntegration/SpecialNormalCoprime.lean`
- `DeepWiki/SymbolicIntegration/Computable/SplitFactorHelpers.lean`
- `Sources/Doi_10_1007_b138171/Chapter3.lean`

The root aggregator will continue importing the moved declarations through `Assembly`.

## Unify list

- Keep classification predicates and split-factor proofs in their existing concept leaves.
- Put final rational-function assembly in `CanonicalRepresentation.Assembly`.
- Leave `CanonicalRepresentation.lean` as a pure import spine.

## Steps

1. Add `CanonicalRepresentation/Assembly.lean` with the moved declarations.
2. Replace the root `CanonicalRepresentation.lean` declaration body with imports, including
   `CanonicalRepresentation.Assembly`.
3. Gate `CanonicalRepresentation.Assembly`, the root aggregator, direct import consumers, the
   Chapter 3 catalog, and the full project.
