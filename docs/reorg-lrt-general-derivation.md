# Reorg: generalized LRT derivation support

Target module:
  `DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LrtGeneralDerivation`

Decls to move:
  `rtResultantGen`, `lrtSubresultantGen`, the general residue/root gcd lemmas,
  general LRT subresultant/gcd correctness lemmas, base-change lemmas, and monic
  normalization helpers currently in `DeepWiki.SymbolicIntegration.LrtGeneralDerivation`.

Impact (`wiki rdeps`):
  `lazardRiobooTrager_output_isSimilar_gcd_gen` is used by
  `isSimilar_subresultant_prod`, then `Computable.LrtSoundness.evalLrtArg_eq_fiber_prod`.
  The module is imported directly by `Computable.LrtSoundness`,
  `Computable.SubresultantTowerSpec`, and `Computable.ResidueResultantTowerSpec`.

Unify:
  No declaration unification in this move. The derivative-specialized residue
  file stays root-level as general rational-integration API; this move only
  puts the generalized LRT machinery under the Rothstein-Trager directory.

Steps:
  1. Move `LrtGeneralDerivation.lean` into
     `RationalIntegrationAlgorithms/RothsteinTrager/`.
  2. Import the moved module from the Rothstein-Trager aggregator.
  3. Rewrite direct imports in computable consumers and the topic root.
  4. Gate the moved module, the computable consumers, and the full library.
  5. Rebuild the wiki graph and commit.
