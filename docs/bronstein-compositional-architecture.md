# Bronstein compositional integration architecture

## Objective

Refactor the transcendental engine around Bronstein Figure 5.1: shared Hermite,
polynomial, and residue reductions feed a monomial-case solver, which reduces
remaining obligations recursively to the coefficient field. The generic assembler
depends only on executable stage interfaces and `Lawful…` contracts.

## Current verified pieces

- Leaf operation/law splits exist for fractions, gcd, Euclidean division, squarefree
  decomposition, resultants, and subresultants.
- `Assemble.lean` now proves `combineSN_isIntegralResultP` once for every lawful polynomial
  representation; the former `DensePoly` theorem is a specialization through `toPoly_list_eq`.
- `CMonomialCase P` is now the representation-parameterized, Prop-free operation interface used by
  dense and recursive realizers; `LawfulCMonomialCase` separates its soundness, denominator preservation,
  and special-part relative-completeness contract.
- `CCanonicalRepresentation` and `LawfulCCanonicalRepresentation` expose canonical decomposition and its
  reconstruction/nonzero/properness laws; `canonicalRepresentationFast` is the dense realizer.
- `LawfulHermiteReduction` and `LawfulResidueLogPart` are representation-neutral stage-result
  contracts; the selected dense realizations cross `toPoly_list_eq` explicitly.
- `LawfulRischLevelLrt` already packages the recursive LRT-level special and reduced contracts.

## Leaf inventory

| Capability | Executable interface | Lawful contract | Realization location |
|---|---|---|---|
| Fractions | `CFrac` | `LawfulCFrac` | `ComputableAlgebra/Fraction.lean` and representation modules |
| Polynomial engine | `CPolyEngine` | `LawfulCPolyEngine` | `ComputableAlgebra/PolyEngine*.lean` |
| GCD | `CPolyGcd` | `LawfulCPolyGcd` | `ComputableAlgebra/PolyReprGcd.lean` |
| Euclidean division | `CPolyEuclidean` | `LawfulCPolyEuclidean` | `ComputableAlgebra/PolyEuclidean.lean` |
| Squarefree Yun | `CPolySquarefree` | `LawfulCPolySquarefree` | `ComputableAlgebra/PolySquarefree.lean`, semantic law in `Engine/SquarefreeDecomposition.lean` |
| Resultant | `CPolyResultant` | `LawfulCPolyResultant` | `ComputableAlgebra/PolyResultant.lean` |
| Subresultant | `CPolySubresultant` | `LawfulCPolySubresultant` | `Engine/SubresultantSpec.lean` |
| Interpolation | `CPolyInterpolate` | `LawfulCPolyInterpolate` | `ComputableAlgebra/PolyInterpolate.lean` |
| Linear solve | `CLinearSolve` | `LawfulCLinearSolve` | `ComputableAlgebra/LinearAlgebra.lean` |

Therefore the first architectural refactor is **not** another leaf abstraction. It is to make the
existing leaf contracts the only dependencies of the canonical, Hermite, polynomial, residue, and
monomial stage contracts.

## Migration order

1. Inventory every public assembler and proof that mentions a concrete dense/Wf operation; use
   `scripts/wiki rdeps` before changing it. Classify each declaration as a stage contract,
   a realization, or obsolete duplicated wiring.
2. Generalize the Stage-1 result data and monomial case from `DensePoly` to a polynomial
   representation parameter `P`. The representation-neutral recombination square and
   `CMonomialCase`/`LawfulCMonomialCase` split are complete; next materialize lawful dense
   realizations and make the generic assembler consume the contracts rather than dense hypotheses.
3. Introduce paired executable/lawful interfaces for canonical representation and polynomial
   reduction. Canonical representation is paired and densely realized; Hermite and residue result
   laws are representation-neutral, but still need Prop-free operation interfaces before the generic
   assembler can select them.
4. Define one generic Figure-5.1 one-level assembler and prove its soundness from only the stage
   contracts. Add a relative-completeness theorem parameterized by complete stage capabilities.
5. Materialize primitive, hyperexponential, and tangent realizers. Move their concrete proofs next
   to their executable operations and make the old full drivers corollaries.
6. Lift the same contract composition through `LawfulRischLevel` / `LawfulRischLevelLrt` for tower
   recursion, then prove full soundness and relative completeness by depth induction.
7. After each replacement, delete the superseded dense/Wf assembly path; retain no internal shim.

## Visibility policy

- `private`: recursion kernels, simulation bridges, proof-local algebra.
- Public: selected executable operation, its `Lawful…` class, and one realization theorem.
- `protected`: only when qualified access is the useful public spelling; namespace qualification alone
  is preferred for ordinary helpers.

## Gates

For each phase: touched module, direct assembler/realizer consumer, bare `scripts/check.sh`, then a
`scripts/wiki rdeps` deadness check before retirement.
