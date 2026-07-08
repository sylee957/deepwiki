# Laurent root bridge reorg

## Target module

Rename `DeepWiki.SymbolicIntegration.LaurentCoefficients.RootSubstitution` to
`DeepWiki.SymbolicIntegration.LaurentCoefficients.RootBridge`.

## Decls to move

None. This is a pure module rename of an import-only bridge aggregator.

## `wiki rdeps` impact

`scripts/wiki rdeps` has no declaration node for the module, because the file contains no
declarations. Text import search shows the only direct consumer is:

- `DeepWiki/SymbolicIntegration/LaurentCoefficients/Assembly.lean`

## Unify list

- Keep the staged declaration ladder:
  - `Base`
  - `FractionInvariant`
  - `RootInvariant`
  - `RootEvaluation`
  - `TaylorCoefficient`
  - `RootBridge`
  - `Assembly`
- Use `RootBridge` for the import-only module that exposes the complete root-evaluation
  and Taylor-coefficient bridge stack to assembly.

## Steps

1. Rename `LaurentCoefficients/RootSubstitution.lean` to
   `LaurentCoefficients/RootBridge.lean`.
2. Update `Assembly.lean` to import `RootBridge`.
3. Gate `DeepWiki.SymbolicIntegration.LaurentCoefficients.RootBridge`,
   `DeepWiki.SymbolicIntegration.LaurentCoefficients.Assembly`, and the full project.
