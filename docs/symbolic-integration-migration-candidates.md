# Symbolic Integration Migration Candidates

Small notes for semantic consolidation targets discovered during the migration.

## Fraction-field quotient rules

- Done: `Core/Differential/PolynomialFractionDeriv.lean` contains the shared
  `PolynomialFractionDeriv` API extending a derivation on `F[X]` to any fraction field of
  `F[X]`.
- Done: `LiouvilleLog.lean` and `LiouvilleExpExtension.lean` now import that API
  instead of carrying parallel `fracDerivFun`/`fracDerivHom`/`fracDeriv` sections.
- `Core/Differential/DifferentialPolynomials.lean` now contains the `DiffPoly`-specific
  quotient-rule derivation `fracDeriv`/`fracKDeriv`; keep it separate because its carrier is
  `FractionRing (DiffPoly K)`, not a fraction field of `F[X]`.
- Remaining candidate: compare the computable tower quotient-rule API in
  `Computable/FractionFieldDeriv.lean` against the abstract `PolynomialFractionDeriv` naming,
  but do not merge the layers unless it becomes a denotation square.

## Differential substitutions

- Done: `diffSubst`, its generator simp lemmas, `diffSubst_ddx`, and the point-evaluation
  helpers now live in `Core/Differential/DifferentialPolynomials.lean`.

## Local principal parts

- Done: the source-neutral local inverse/approximant/coefficient/principal-part construction
  now lives in `Core/Polynomial/LocalPrincipalParts.lean`.
- Done: local regularity, uniqueness, coefficient-derivative readings, and closure-level
  principal-part assembly live in the `Core/Polynomial/LocalPrincipal*.lean` files.
- Remaining boundary: keep the Laurent-engine bridge theorems in `LaurentCoefficients.lean`
  unless they become reusable outside the Laurent substitution engine.
