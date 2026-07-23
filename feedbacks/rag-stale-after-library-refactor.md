# `scripts/wiki` silently reports declarations removed by a recent refactor

- **Date:** 2026-07-10
- **Tool/step:** `scripts/wiki show` and `scripts/wiki rdeps`
- **Expected:** Dependency queries reflect the current compiled library or clearly report that the graph is stale.
- **Actual:** After commit `60417898`, the graph still listed removed declarations such as `gbdegCore`, `gbisZeroCore`, and the retired rational log-argument wrappers. Attempting `scripts/wiki build` then failed because `.lake/build/lib/lean/DeepWiki/SymbolicIntegration/Engine/CoupledDE/Assembly.olean` did not exist. On 2026-07-11, `rdeps CFrac.reduceGcd` likewise reported the deleted `Engine/QFunReduce.lean` until an explicit `scripts/wiki build` refresh. After moving `Engine.LinearSolveCorrect` to `ComputableAlgebra.LinearAlgebraRatCorrect`, `scripts/wiki build` first loaded the obsolete `.olean` and failed with a duplicate private declaration already present in the new module; after removing stale artifacts, it exposed a source catalog import of the retired module that the `DeepWiki`-only gate had not checked. Later that day, after replacing `DensePoly.MonomialCase` with `CMonomialCase`, `scripts/wiki build` exited successfully but `rdeps` still reported the retired declaration and could not find the new one. The same stale graph later reported retired `oneLevelRischWithPolynomial` and `assembleOneLevelWithPolynomial` as live although `rg` found neither source declaration nor consumer. On 2026-07-12, after a successful `scripts/wiki build` and a full strict gate, `rdeps cIntegrateHyperexpFull` still reported the deleted full driver, its deleted soundness theorem, and its deleted example from `Hyperexp/FullSoundness.lean` and `Hyperexp/Normal.lean`. On 2026-07-15, moving the dependent-calculus modules under `Refine/CCOmega/` and successfully running both the full gate and `scripts/wiki build` still left `show DependentCalculus.Term` pointing at deleted `DeepWiki/Refine/DependentCalculusSyntax.lean`, while the new `CCOmega.SurfaceSyntax.expandTerm` declaration was absent.
- **Additional occurrence:** On 2026-07-23,
  `rdeps DeepWiki.SymbolicIntegration.implicitDeriv_X_quotientSpanX` reported no matching
  declaration even though the theorem had compiled in the current source.
- **Additional occurrence:** On 2026-07-23, `rdeps DeepWiki.SymbolicIntegration.kappaD`
  reported the declaration and its callers under
  `DeepWiki/SymbolicIntegration/DifferentialAlgebraFacts/Rao.lean`, a path absent from the
  current tree; the declaration was actually in `RaoDifferentialPolynomials.lean`.
- **Why it's a limitation:** The graph database is not invalidated when library source or build artifacts change, so structurally plausible but obsolete results are returned without a warning.
- **Workaround used:** Confirm against current source, use `rg` for reverse-dependency checks, rebuild the affected library, and delete obsolete `.olean`/`.ilean` artifacts for retired module paths before rebuilding the graph.
- **Suggested fix:** Store the library/source fingerprint used to build the graph and make query commands warn or fail when it differs from the current checkout.
- **Status:** open
