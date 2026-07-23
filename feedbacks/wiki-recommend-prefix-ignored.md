# `wiki recommend` does not constrain recommendations to the requested prefix

- **Date:** 2026-07-18
- **Tool/step:** `scripts/wiki recommend --prefix DeepWiki.Refine.DependentCalculus.UnivalentParametricity --seed 20260718 --k 8`
- **Expected:** Sample a structural action whose declarations lie under the requested univalent-parametricity prefix.
- **Actual:** The command reported that six action types live under `DeepWiki.SymbolicIntegration` and sampled a SymbolicIntegration merge action. On 2026-07-23,
  `scripts/wiki recommend --prefix DeepWiki.SymbolicIntegration.DifferentialAlgebra`
  likewise recommended moving `fieldFrac` between integration-engine modules outside
  `DifferentialAlgebra/`.
- **Why it's a limitation:** The requested prefix is not reaching or not constraining the recommendation query, so the structural signal cannot be used for the scoped audit.
- **Workaround used:** Inspect the current module DAG, source boundaries, file sizes, and declaration dependencies directly.
- **Suggested fix:** Validate `--prefix` parsing and filter candidate actions before sampling; report an empty scoped front when no action exists.
- **Status:** open
