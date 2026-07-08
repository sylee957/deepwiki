# Core aggregator reorganization

## Target modules

- Add `DeepWiki.SymbolicIntegration.Core.Algebra` as the index for abstract algebra support.
- Add `DeepWiki.SymbolicIntegration.Core.Polynomial` as the index for polynomial, rational-function, squarefree, and Groebner support.
- Add `DeepWiki.SymbolicIntegration.Core.Differential` as the index for derivations, differential polynomials, implicit-derivative facts, and normal/special decomposition support.
- Add `DeepWiki.SymbolicIntegration.Core` as the single random-access entry point for the carrier-neutral core.

## Declarations to move

None. This is an aggregator-only reorganization. Existing declarations stay in their defining files.

## Impact check

- `scripts/wiki rdeps DeepWiki.SymbolicIntegration.IsGCD --depth 2` shows the abstract gcd API is consumed from `Core.Algebra.GcdBasics` by catalog entries and polynomial/differential support.
- The topic root currently imports every `Core/*` leaf directly, so readers cannot import or browse the core by area.
- The change replaces those leaf imports in `DeepWiki.SymbolicIntegration` with `DeepWiki.SymbolicIntegration.Core`.

## Unify list

- `Core.Algebra` imports `Core.Algebra.GcdBasics`.
- `Core.Polynomial` imports all direct polynomial support leaves and the `Groebner` support leaves.
- `Core.Differential` imports all direct differential support leaves and existing sub-aggregators.
- `Core` imports `Core.Algebra`, `Core.Polynomial`, and `Core.Differential`.

## Steps

1. Add the four aggregators with module docstrings.
2. Replace the corresponding leaf imports in `DeepWiki/SymbolicIntegration.lean` with `import DeepWiki.SymbolicIntegration.Core`.
3. Gate `DeepWiki.SymbolicIntegration.Core`, then full `scripts/check.sh`.
4. Rebuild the wiki graph.
