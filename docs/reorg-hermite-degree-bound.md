# Reorg: algebraic Hermite degree bound

Target module: `DeepWiki.SymbolicIntegration.Computable.Algebraic.HermiteDegreeBound`

Decls to move:
- `hermiteBoundN`
  `Computable/Algebraic/AlgebraicHermiteCompleteness.lean` -> `Computable/Algebraic/HermiteDegreeBound.lean`
- `hermiteCandTopDegree`
  `Computable/Algebraic/AlgebraicHermiteCompleteness.lean` -> `Computable/Algebraic/HermiteDegreeBound.lean`
- `natDegree_le_hermiteCandTopDegree`
  `Computable/Algebraic/AlgebraicHermiteCompleteness.lean` -> `Computable/Algebraic/HermiteDegreeBound.lean`
- `natDegree_hermiteNum_le_of_topCoeff_ne_zero`
  `Computable/Algebraic/AlgebraicHermiteCompleteness.lean` -> `Computable/Algebraic/HermiteDegreeBound.lean`
- `natDegree_hermiteNum_le`
  `Computable/Algebraic/AlgebraicHermiteCompleteness.lean` -> `Computable/Algebraic/HermiteDegreeBound.lean`
- `implicitDeriv_X2_X`
  `Computable/Algebraic/AlgebraicHermiteCompleteness.lean` -> `Computable/Algebraic/HermiteDegreeBound.lean`
- `hermite_degree_bound_witness`
  `Computable/Algebraic/AlgebraicHermiteCompleteness.lean` -> `Computable/Algebraic/HermiteDegreeBound.lean`

Impact:
- `hermiteCandTopDegree` is used by Schultz/Trager source aliases and the concrete witness.
- `hermiteBoundN` is used by the Schultz/Trager source alias `eq_4_9_degreeBound`.
- The moved proofs depend on `natDegree_implicitDeriv_le` from `MonomialExtensions`.
- `AlgebraicHermiteCompleteness` should import the new module so downstream names stay available
  through the old aggregate import.

Unify:
- No duplicate theorem to retire. The improvement is file ownership: degree-bound definitions and
  examples become a standalone Hermite support API, while `AlgebraicHermiteCompleteness` focuses on
  pole conditions, finite-place uniqueness, and frontier reduction.

Steps:
1. Create `HermiteDegreeBound.lean` with the degree-bound section and witness.
2. Import it from `AlgebraicHermiteCompleteness.lean` and remove the moved sections there.
3. Import the new module from the Algebraic aggregator.
4. Gate the new module, old module, Schultz catalog target, then full check.
