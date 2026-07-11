# Bronstein compositional integration architecture

## Objective

Refactor the transcendental engine around Bronstein Figure 5.1: shared Hermite,
polynomial, and residue reductions feed a monomial-case solver, which reduces
remaining obligations recursively to the coefficient field. The generic assembler
depends only on executable stage interfaces and `Lawful…` contracts.

## Current verified pieces

- Leaf operation/law splits exist for fractions, gcd, Euclidean division, squarefree
  decomposition, resultants, and subresultants.
- `Assemble.lean` already contains a concrete-algorithm-free combination theorem.
- `LawfulHermiteReduction` and `LawfulResidueLogPart` exist as stage-result contracts.
- `LawfulRischLevelLrt` already packages the recursive LRT-level special and reduced contracts.

## Migration order

1. Inventory every public assembler and proof that mentions a concrete dense/Wf operation; use
   `scripts/wiki rdeps` before changing it. Classify each declaration as a stage contract,
   a realization, or obsolete duplicated wiring.
2. Generalize the Stage-1 result data and `MonomialCase` from `DensePoly` to a polynomial
   representation parameter `P`. Keep dense consumers as instances/realizers.
3. Introduce paired executable/lawful interfaces for canonical representation and polynomial
   reduction; fold existing Hermite and residue contracts into the same stage vocabulary.
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
