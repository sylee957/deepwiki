# Implicit derivation degree reorganization

## Target module

Create `DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivDegree` for degree bounds about
`Differential.implicitDeriv`, and leave `ImplicitDerivLinearFactors` focused on linear-factor criteria,
factorizations, and gcd formulas.

## Declarations to move

- `natDegree_implicitDeriv_le`
- `natDegree_implicitDeriv_eq`

## Impact

`scripts/wiki rdeps` shows the degree lemmas are consumed by:

- `Sources.Doi_10_1007_b138171.Chapter3`
- `AlgebraicHermiteDegreeBound`
- `MonomialConstants.{Scalar,Nonlinear}`
- `Computable.RischDE.DegreeBound`
- `Computable.NormalPartSoundness`

The old import path `Core.Differential.ImplicitDerivLinearFactors` will continue to import the new degree
leaf, so existing downstream imports stay valid.

## Unify list

- Keep theorem names, statements, and proof bodies unchanged.
- Put general degree estimates in `ImplicitDerivDegree`.
- Keep linear-factor normal/special criteria and gcd formulas in `ImplicitDerivLinearFactors`.

## Steps

1. Add `ImplicitDerivDegree.lean` with the two degree theorems.
2. Import it from `ImplicitDerivLinearFactors.lean` and remove the duplicate declarations there.
3. Gate the new leaf, the old linear-factor module, the direct consumers, and the full repository.
4. Rebuild the wiki graph and commit.
