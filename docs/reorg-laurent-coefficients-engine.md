# Laurent-coefficient engine reorganization

## Target modules

- `DeepWiki.SymbolicIntegration.LaurentCoefficients.Base`
- `DeepWiki.SymbolicIntegration.LaurentCoefficients.Engine`
- existing downstream leaves continue importing the same higher-level path chain.

## Declarations to move

Move the engine-output layer from `Base` to `Engine`:

- `laurentSubst`
- `laurentQ`
- `laurentH`
- `laurentH_def`

## `wiki rdeps` impact

- `laurentSubst` is used by `laurentQ` and by root-evaluation bridges.
- `laurentQ` and `laurentH` are the engine output definitions used by root evaluation and assembly examples.
- Moving the group together avoids sending `Base` to import `RootEvaluation` and keeps the dependency direction `Base -> Engine -> RootEvaluation`.

## Unify list

- `Base` should hold cofactors and numerator-recursion ingredients.
- `Engine` should hold the executable algebraic output definitions built from those ingredients.
- `RootEvaluation` should import `Engine` when proving root-value properties of the output.

## Steps

1. Add `Engine.lean` importing `Base`.
2. Move the four output definitions from `Base` to `Engine` unchanged.
3. Update `RootEvaluation` to import `Engine`.
4. Gate `Base`, `Engine`, `RootEvaluation`, `Assembly`, and the full repository.
5. Rebuild the wiki graph and commit the split.
