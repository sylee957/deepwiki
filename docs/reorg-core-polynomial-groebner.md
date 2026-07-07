# Reorg: Core polynomial Groebner cluster

Target module family: `DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.*`

Move the flat `Core/Polynomial/Groebner*.lean` files into a `Groebner/`
subdirectory and drop the repeated `Groebner` prefix from leaf module names. This
keeps declaration namespaces and names unchanged while making the path encode the
concept family.

Decls/modules to move:
- `GroebnerBasisBasic.lean` -> `Groebner/BasisBasic.lean`
- `GroebnerBasisExistence.lean` -> `Groebner/BasisExistence.lean`
- `GroebnerBivariateSorting.lean` -> `Groebner/BivariateSorting.lean`
- `GroebnerBivariateView.lean` -> `Groebner/BivariateView.lean`
- `GroebnerBoundedReduction.lean` -> `Groebner/BoundedReduction.lean`
- `GroebnerBuchbergerAlgorithm.lean` -> `Groebner/BuchbergerAlgorithm.lean`
- `GroebnerBuchbergerCriterion.lean` -> `Groebner/BuchbergerCriterion.lean`
- `GroebnerCommonFactor.lean` -> `Groebner/CommonFactor.lean`
- `GroebnerDivideOutCommonFactor.lean` -> `Groebner/DivideOutCommonFactor.lean`
- `GroebnerDividedBasis.lean` -> `Groebner/DividedBasis.lean`
- `GroebnerLazardDescent.lean` -> `Groebner/LazardDescent.lean`
- `GroebnerLazardFactorization.lean` -> `Groebner/LazardFactorization.lean`
- `GroebnerLazardStep.lean` -> `Groebner/LazardStep.lean`
- `GroebnerLeadingYCoeffGcd.lean` -> `Groebner/LeadingYCoeffGcd.lean`
- `GroebnerNoCommonYFactor.lean` -> `Groebner/NoCommonYFactor.lean`
- `GroebnerOneVariableGcd.lean` -> `Groebner/OneVariableGcd.lean`
- `GroebnerReducedBasis.lean` -> `Groebner/ReducedBasis.lean`
- `GroebnerReductionStep.lean` -> `Groebner/ReductionStep.lean`
- `GroebnerSPolynomial.lean` -> `Groebner/SPolynomial.lean`

Impact:
- `wiki rdeps IsGroebnerBasis --depth 2` shows broad dependents in the Groebner
  cluster, `GroebnerBasis.lean`, `CzichowskiNormalPosition.lean`, and Sources
  catalogs. Because declarations remain in namespace `DeepWiki.SymbolicIntegration`,
  only imports change.
- Direct import callers found by `rg "import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner"`:
  internal Groebner modules and `DeepWiki/SymbolicIntegration/GroebnerBasis.lean`.

Unify:
- None in this structural commit. This is a pure module-path split; content
  changes can follow after the path boundary is stable.

Steps:
1. `git mv` the Groebner files into `Core/Polynomial/Groebner/`.
2. Rewrite imports from `Core.Polynomial.GroebnerFoo` to
   `Core.Polynomial.Groebner.Foo`.
3. Gate `DeepWiki.SymbolicIntegration.GroebnerBasis`.
4. Run the full gate.
5. Rebuild the wiki graph and commit the pure move.
