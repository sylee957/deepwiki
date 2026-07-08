# Rational Integration Algorithms Leaf Split

## Target modules

- `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.Hermite`
- `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.PolynomialPart`
- `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.Horowitz`

## Declarations to move

- Hermite: `hermiteReduce_sum_spec`, `hermiteReduce_full`
- Polynomial part: `polyIntegral`, `polyIntegral_derivative`,
  `ratFunc_polyDivide_split`, `integrateRationalFunction_reduction`,
  `integrateRationalFunction_reduction_proper`
- Horowitz: `hoSplit`, `hoSplit_mul`, `hoSplit_snd_squarefree`,
  `hoSplit_fst_dvd_deriv_mul_snd`, `horowitzReduce_step_ratFunc`

## Impact

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.hermiteReduce_full --depth 2`
shows the source alias and the polynomial-part reduction theorem.
`scripts/wiki rdeps DeepWiki.SymbolicIntegration.integrateRationalFunction_reduction --depth 2`
shows the source alias. `scripts/wiki rdeps DeepWiki.SymbolicIntegration.hoSplit --depth 2`
shows the source aliases in the Bronstein chapter and Horowitz-method paper catalog plus the
local Horowitz lemmas.

## Unify list

- Keep `RationalIntegrationAlgorithms.lean` as an import-only aggregator.
- Put Hermite assembly beside `HermitePower`.
- Put polynomial antiderivatives and division-based rational-function reductions in
  `PolynomialPart`.
- Put the Horowitz-Ostrogradsky denominator split and transported rational-function identity
  in `Horowitz`.

## Steps

1. Create the three leaf modules and move declarations without changing signatures or proofs.
2. Replace the root file with imports of all algorithm leaves.
3. Gate each leaf, then the root, source catalog aliases, and the full library.
