# Symbolic Integration Migration Candidates

Small notes for semantic consolidation targets discovered during the migration.

## Fraction-field quotient rules

- `LiouvilleLogExtension.lean` and `LiouvilleExpExtension.lean` each define a parallel
  `fracDerivFun`/`fracDerivHom`/`fracDeriv` quotient-rule extension from `F[X]` to its fraction
  field.
- `Core/Differential/DifferentialPolynomials.lean` now contains the `DiffPoly`-specific
  quotient-rule derivation `fracDeriv`/`fracKDeriv`.
- Candidate: factor the repeated "extend a polynomial derivation to a fraction field by the
  quotient rule" API into a source-neutral differential core file, then make the Liouville and
  `DiffPoly` constructions thin specializations.

## Differential substitutions

- Done: `diffSubst`, its generator simp lemmas, `diffSubst_ddx`, and the point-evaluation
  helpers now live in `Core/Differential/DifferentialPolynomials.lean`.

## Local principal parts

- `LaurentCoefficients.lean` still contains the local inverse/approximant/principal-part API:
  `localInverse`, `localApprox`, `localCoeff`, `localPrincipalPart`, and regularity/uniqueness
  lemmas.
- Candidate: extract the source-neutral local principal-part construction into a polynomial
  or rational-function core file, leaving only the bridge to the Laurent engine in
  `LaurentCoefficients.lean`.
