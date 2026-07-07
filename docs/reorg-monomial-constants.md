# Monomial constants split

## Target modules

- `DeepWiki.SymbolicIntegration.MonomialConstants.Basic`
- `DeepWiki.SymbolicIntegration.MonomialConstants.Nonlinear`
- `DeepWiki.SymbolicIntegration.MonomialConstants.Scalar`
- `DeepWiki.SymbolicIntegration.MonomialConstants.ConstantField`
- `DeepWiki.SymbolicIntegration.MonomialConstants.BaseChange`
- `DeepWiki.SymbolicIntegration.MonomialConstants` remains the public aggregator.

## Declarations to move

`Basic`:

- `isSpecial_of_coprime_of_deriv_quotient_num_eq_zero`
- `isSpecial_num_denom_of_const_quotient`

`Nonlinear`:

- `leadingCoeff_implicitDeriv_nonlinear`
- `leadingCoeff_cofactor_nonlinear`
- `natDegree_eq_of_special_of_deriv_quotient_num_eq_zero`
- `isSpecial_and_natDegree_eq_of_const_quotient_nonlinear`

`Scalar`:

- `natDegree_implicitDeriv_C_le`
- `coeff_natDegree_implicitDeriv_C`
- `deriv_monic_eq_zero_or_natDegree_lt`
- `isSpecial_iff_deriv_eq_zero_of_monic`
- `associated_mul_C_inv_leadingCoeff`
- `isSpecial_iff_deriv_normalize_eq_zero`

`ConstantField`:

- `dvd_X_sub_C_implicitDeriv_iff_dvd`
- `dvd_prod_X_sub_C_implicitDeriv_iff_dvd`
- `isCoprime_prod_X_sub_C_implicitDeriv_iff_isCoprime`

`BaseChange`:

- `isCoprime_map_implicitDeriv_of_isCoprime`

## Impact

This is a file-mode split. The local modularity sample reports
`MonomialConstants` as one cohesive file but with three structural communities.
The public import path remains `DeepWiki.SymbolicIntegration.MonomialConstants`,
so downstream modules should not need import edits.

## Unify list

- Keep quotient-special facts in `Basic`.
- Put nonlinear degree comparisons in `Nonlinear`.
- Put scalar derivation and monic-normalization facts in `Scalar`.
- Put constant-scalar linear-factor tests in `ConstantField`.
- Put the base-change coprimality bridge in `BaseChange`.

## Steps

1. Add the stage modules under `MonomialConstants/`.
2. Replace `MonomialConstants.lean` with an aggregator importing `BaseChange`,
   `Nonlinear`, and `Scalar`.
3. Gate each new module, then the public aggregator.
4. Run the full gate, rebuild the wiki graph, and commit.
