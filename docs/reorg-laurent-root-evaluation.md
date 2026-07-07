# Reorg: Laurent root-evaluation bridge

## Target module

`DeepWiki.SymbolicIntegration.LaurentCoefficients.RootEvaluation`

`Base.lean` should define the Laurent-coefficient engine primitives. Root evaluation
facts, including the simple-root residue specialization, belong beside the existing
general root-evaluation bridge.

## Decls to move

Move unchanged from `LaurentCoefficients.Base` to `LaurentCoefficients.RootEvaluation`:

- `aeval_laurentSubst_dpEmbed`
- `laurentQ_one_one`
- `laurentE_one`
- `laurentH_one_one`
- `eval_modByMonic_of_root`
- `bezoutE_mul_laurentE_eval`
- `bezoutDeriv_mul_derivative_eval`
- `eval_laurentH_one_one`
- `eval_laurentH_one_one_eq_residue`

## Impact from `scripts/wiki rdeps`

- `eval_laurentH_one_one_eq_residue` is used by
  `Sources.Doi_10_1007_b138171.Chapter2.thm_2_7_1_residue`.
- `eval_laurentH_one_one` is used by `eval_laurentH_one_one_eq_residue`.
- `eval_modByMonic_of_root`, `bezoutE_mul_laurentE_eval`, and
  `bezoutDeriv_mul_derivative_eval` are also used by the existing
  `RootEvaluation.eval_laurentH` theorem, so move them before that theorem.

## Unify list

- Keep engine definitions and congruence facts in `Base`.
- Keep all root-value and residue evaluation facts in `RootEvaluation`.
- Do not change declaration names, statements, proofs, or namespaces.

## Steps

1. Move the block from `Base` to `RootEvaluation`.
2. Gate `LaurentCoefficients.Base`, `LaurentCoefficients.RootEvaluation`, the Laurent
   aggregator, and the source catalog chapter.
3. Run the full gate, rebuild the wiki graph, and commit.
