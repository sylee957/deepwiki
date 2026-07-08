# Reorg: Liouville structure API

Target modules:
  `DeepWiki.SymbolicIntegration.LiouvilleStructure`
  `DeepWiki.SymbolicIntegration.LiouvilleStructure.Core`
  `DeepWiki.SymbolicIntegration.LiouvilleStructure.MonomialDeriv`

Decls to move:
  The weak-Liouville-form predicate and descent/frontier theorems from
  `Computable.LiouvilleStructure.Core`, plus the log/exp monomial-derivation
  degree lemmas from `Computable.LiouvilleStructure.MonomialDeriv`.

Impact (`wiki rdeps`):
  `HasWeakLiouvilleForm` is used by the algebraic-completeness frontier wrapper
  and by the Kaltofen/Rosenlicht source catalogs. The monomial top-coefficient
  lemmas are source-catalog-facing (`Kal.lemma_3_1a`, `Kal.lemma_3_1b`).

Unify:
  No declaration unification in this move. The point is placement: these are
  abstract Liouville-structure theorems over Mathlib carriers, not executable
  computable-engine modules.

Steps:
  1. Move the `Computable/LiouvilleStructure` directory and aggregator to the
     topic root as `LiouvilleStructure`.
  2. Rewrite imports in `Computable.lean`, `AlgebraicCompleteness/LiouvilleFrontier.lean`,
     and source catalogs.
  3. Gate the moved aggregator, the algebraic-completeness wrapper, both source
     catalogs, and the full project.
  4. Rebuild the wiki graph and commit.
