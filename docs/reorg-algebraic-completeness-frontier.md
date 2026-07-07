# Algebraic Completeness Frontier Reorg

## Target module

`DeepWiki.SymbolicIntegration.AlgebraicCompleteness.Frontier`

Aggregator:

`DeepWiki.SymbolicIntegration.AlgebraicCompleteness`

## Declarations to move

From `DeepWiki.SymbolicIntegration.Computable.Algebraic.AlgebraicCompleteness`:

- `IsAlgebraicElementary`
- `elementary_base_of_elementary_finiteDim`
- `not_elementary_extension_of_not_elementary_base_alg`
- `AlgebraicLiouvilleFrontier`
- `algebraicLiouville_single_extension`
- `ratPart_isAlgebraicElementary`
- `RationalPartExhaustivenessFrontier`

## Impact check

- `scripts/wiki rdeps IsAlgebraicElementary --depth 2`
  - consumed by Hermite completeness, Liouville frontier, Rosenlicht source catalog, and local frontier theorems.
- `scripts/wiki rdeps AlgebraicLiouvilleFrontier --depth 2`
  - consumed by Liouville frontier and Rosenlicht source catalog.
- `scripts/wiki rdeps RationalPartExhaustivenessFrontier --depth 2`
  - consumed by Hermite completeness and Schultz-Trager source catalog.
- `scripts/wiki rdeps ratPart_isAlgebraicElementary --depth 2`
  - no downstream consumers outside the moved abstract layer.

## Unify list

- Keep abstract Liouville/frontier predicates in the top-level algebraic-completeness namespace.
- Leave executable torsion witnesses, `native_decide` examples, and engine residuals in the existing `Computable/Algebraic/AlgebraicCompleteness.lean` file.
- Update abstract consumers to import the new top-level aggregator instead of the computable engine module.

## Steps

1. Create `AlgebraicCompleteness/Frontier.lean` and `AlgebraicCompleteness.lean`.
2. Move the abstract sections and their restatement/axiom audit entries to the new frontier module.
3. Import the top-level aggregator from the old computable module and abstract consumers.
4. Gate the new frontier module, the old computable module, affected abstract/source consumers, then the full project.
5. Rebuild the wiki graph and commit.
