# Reorganize algebraic preliminaries

## Target modules

- `DeepWiki.SymbolicIntegration.Core.Algebra.GcdBasics`
  - `IsGCD`
  - `IsGCD.dvd_left`
  - `IsGCD.dvd_right`
  - `IsGCD.dvd`
  - `IsGCD.symm`
  - `IsGCD.associated`
  - `associated_gcd_mul_of_isUnit_gcd`
  - `dvd_of_dvd_mul_of_isUnit_gcd`
  - `associated_gcd_mul_left_cancel`
  - `isUnit_gcd_prod`
  - `associated_gcd_add_mul`
- `DeepWiki.SymbolicIntegration.Core.Polynomial.ResultantRoots`
  - `resultant_eq_zero_iff_exists_root`

## Why

`AlgebraicPreliminaries` currently mixes an abstract gcd/divisibility API with a polynomial resultant
root criterion at the root of `SymbolicIntegration`. Random access is clearer if abstract algebra
support lives under `Core.Algebra`, while the resultant theorem lives with the polynomial core.

## Impact

- `IsGCD`: catalog chapter 1 aliases and `Core.Polynomial.SquarefreeDerivative`.
- `resultant_eq_zero_iff_exists_root`: `Sources/Doi_10_1007_b138171/Chapter1.lean`.
- GCD-multiplicativity and cancellation lemmas: `MonomialExtensions` and downstream
  `CanonicalRepresentation` catalog aliases.

## Unify List

- Keep declaration names and namespaces unchanged.
- Replace direct imports of `AlgebraicPreliminaries` with the focused module needed by each consumer.
- Remove the root-level grab-bag module once all imports are updated.

## Steps

1. Add `Core/Algebra/GcdBasics.lean` with the abstract gcd API and `Core/Polynomial/ResultantRoots.lean`
   with the resultant-root theorem.
2. Update topic and catalog imports.
3. Delete `AlgebraicPreliminaries.lean`.
4. Gate affected modules, rebuild the wiki graph, run the full gate, and commit.
