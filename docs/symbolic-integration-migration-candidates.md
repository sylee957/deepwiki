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

- `LaurentCoefficients.lean` defines `diffSubst`, its generator simp lemmas, and
  `diffSubst_ddx`.
- Candidate: move this cluster to the differential-polynomial core once the Laurent-specific
  root evaluation lemmas are separated from the generic differential-hom statement.
