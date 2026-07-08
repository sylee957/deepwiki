# Core Polynomial Aggregators Reorg

## Target module

`DeepWiki.SymbolicIntegration.Core.Polynomial`

## Theme

The root polynomial aggregator currently imports every polynomial support leaf directly.
That makes random access harder because unrelated themes sit in one flat import wall:
linear factors, rational-function support, local principal parts, squarefree/Yun theory,
and Groebner support.

## Decls to move

None. This is an aggregator-only reorganization. All declaration meanings and declaration
modules remain unchanged.

## Impact

- Direct importer of the root aggregator: `DeepWiki.SymbolicIntegration.Core`.
- Leaf consumers already import the specific leaf modules they use.
- The change only adds semantic import entry points and rewires the root aggregator to
  import those entry points.

## Unify list

- `DeepWiki.SymbolicIntegration.Core.Polynomial.Basic`
  - `LinearFactors`
  - `PolynomialNormalization`
  - `RootEvaluation`
  - `ResultantRoots`
- `DeepWiki.SymbolicIntegration.Core.Polynomial.RatFunc`
  - `RatFuncEmbedding`
  - `RatFuncEvaluation`
  - `RatFuncFractions`
  - `RatFuncRegular`
- `DeepWiki.SymbolicIntegration.Core.Polynomial.LocalPrincipal`
  - `LocalPrincipalParts`
  - `LocalPrincipalDerivatives`
  - `LocalPrincipalUniqueness`
  - `LocalRegularity`
  - `LocalPrincipalAssembly`
- `DeepWiki.SymbolicIntegration.Core.Polynomial.Squarefree`
  - `SquarefreeDeflation`
  - `SquarefreeDerivative`
  - `SquarefreePartDerivatives`
  - `SquarefreeParts`
  - `SquarefreeYun`
  - `SquarefreeYunLoop`
- Keep `DeepWiki.SymbolicIntegration.Core.Polynomial.Diophantine` as its own entry point
  because it is a solver theorem cluster used by rational integration and Laurent cofactors.
- Keep the existing Groebner leaf aggregator as the Groebner entry point.
  - Add `DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner` because the
    `Groebner/` directory did not yet have a sibling aggregator.

## Steps

1. Add the four conceptual aggregator modules.
2. Replace the flat `Core/Polynomial.lean` import wall with those aggregators plus
   `Diophantine` and `Groebner`.
3. Gate `DeepWiki.SymbolicIntegration.Core.Polynomial`, then the full `scripts/check.sh`.
4. Rebuild the wiki graph and commit the pure aggregator split.
