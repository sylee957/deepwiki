# Generic squarefree selection law

## Goal

Give the representation-generic `CPolySquarefree.default` Yun loop a denotation proof and use it
to install `LawfulCPolySquarefree CPoly.SparsePoly`. The public selected operation remains
`CPoly.squarefreeYun`; dense tower coefficients retain their well-founded specialization where it
is intentionally selected.

## Established boundary

- `76f8ba19` makes the generic kernel select `CPolyGcd.compute`, rather than treating the first
  component of `CPolyEuclidean.gcdExt` as a gcd without a greatestness law.
- `LawfulCPolyGcd` supplies associatedness to the mathematical gcd; `LawfulCPolyEuclidean`
  supplies exact quotient denotations.
- `CPoly.cdeg_lt_degBound_of_toPoly_ne_zero` supplies enough generic fuel.

## Proof route

1. Prove a generic selected-gcd associatedness bridge and use exact division to relate one
   `defaultGo` transition to `yunLoopAbs`.
2. Prove the initialization pair of `default` is associated to
   `(A / gcd A A', gcd A A')`, using monic normalization only up to associates.
3. Induct on the generic fuel to obtain `List.Forall₂ Associated` between `defaultGo` and the
   abstract Yun loop. Fuel is `degBound`; the honest-degree bound discharges the abstract loop's
   termination requirement.
4. Transport the abstract loop's powered-product reconstruction, monicity, squarefreeness, and
   pairwise-coprimality through the `Forall₂` bridge to build `LawfulSquarefreeDecomposition`.
5. Register the sparse lawful instance and add a sparse semantic consumer/witness. Keep helper
   simulations private; only the selected class law is public.

## Verification

Run `scripts/check.sh DeepWiki.SymbolicIntegration.Engine.PolySquarefree`, then the sparse
consumer and finally bare `scripts/check.sh`. Before retiring or changing any dense bridge, use
`scripts/wiki rdeps` to distinguish the deliberate well-founded specialization from generic
consumers.
