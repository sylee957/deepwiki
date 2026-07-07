# Laurent fraction invariant split

## Target module

`DeepWiki.SymbolicIntegration.LaurentCoefficients.FractionInvariant`

## Declarations to move

- `lDenom`, `lDenom_ne_zero`, `lDenom_succ`
- `hFrac`, `lFrac`, `lFrac_zero`, `lFrac_mk`
- `reduced_num`, `fracKDeriv_lFrac`
- `laurentScale`, `laurentScale_eq_factorial`
- `iterate_fracKDeriv_hFrac`

The private helper `mem_nzd` moves with `lFrac_mk`.

## Impact

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.lDenom --depth 3` reports the
main downstream users in `LaurentCoefficients.RootSubstitution` plus the source
catalog restatement `DeepWiki.Si.eq_2_11_invariant`.

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.iterate_fracKDeriv_hFrac --depth 3`
reports only `DeepWiki.Si.eq_2_11_invariant`.

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.fracKDeriv_lFrac --depth 3`
reports `iterate_fracKDeriv_hFrac` and the same catalog restatement.

`scripts/wiki rdeps DeepWiki.SymbolicIntegration.reduced_num --depth 3` reports
the local fraction-derivative proof and the root-substitution analogues.

## Unify list

- Keep `Base` for the Laurent coefficient engine: cofactors, numerator
  recursion, substitution, `laurentQ`, `laurentH`, and the simple-root residue
  specialization.
- Move the fraction-field recursion invariant to the new module so readers can
  find the `K(x)⟨u⟩` invariant without scanning the engine setup.
- Retarget `RootSubstitution` to import `FractionInvariant`; the public
  aggregator path stays unchanged through `Engine`.

## Steps

1. Add `FractionInvariant.lean` importing `Base`.
2. Move the fraction-invariant block from `Base` unchanged.
3. Change `RootSubstitution.lean` to import the new module.
4. Gate the new module, then `RootSubstitution`, then the full check.
5. Rebuild the wiki graph and commit the logical split.
