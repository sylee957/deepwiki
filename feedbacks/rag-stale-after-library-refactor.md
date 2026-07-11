# `scripts/wiki` silently reports declarations removed by a recent refactor

- **Date:** 2026-07-10
- **Tool/step:** `scripts/wiki show` and `scripts/wiki rdeps`
- **Expected:** Dependency queries reflect the current compiled library or clearly report that the graph is stale.
- **Actual:** After commit `60417898`, the graph still listed removed declarations such as `gbdegCore`, `gbisZeroCore`, and the retired rational log-argument wrappers. Attempting `scripts/wiki build` then failed because `.lake/build/lib/lean/DeepWiki/SymbolicIntegration/Engine/CoupledDE/Assembly.olean` did not exist. On 2026-07-11, `rdeps CFrac.reduceGcd` likewise reported the deleted `Engine/QFunReduce.lean` until an explicit `scripts/wiki build` refresh. After moving `Engine.LinearSolveCorrect` to `ComputableAlgebra.LinearAlgebraRatCorrect`, `scripts/wiki build` first loaded the obsolete `.olean` and failed with a duplicate private declaration already present in the new module; after removing stale artifacts, it exposed a source catalog import of the retired module that the `DeepWiki`-only gate had not checked.
- **Why it's a limitation:** The graph database is not invalidated when library source or build artifacts change, so structurally plausible but obsolete results are returned without a warning.
- **Workaround used:** Confirm against current source, use `rg` for reverse-dependency checks, rebuild the affected library, and delete obsolete `.olean`/`.ilean` artifacts for retired module paths before rebuilding the graph.
- **Suggested fix:** Store the library/source fingerprint used to build the graph and make query commands warn or fail when it differs from the current checkout.
- **Status:** open
