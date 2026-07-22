# Wiki graph build misses an aggregator dependency

- **Date:** 2026-07-11
- **Tool/step:** `scripts/wiki build` after a successful `scripts/check.sh`.
- **Expected:** the graph builder loads the environment built by the full repository gate.
- **Actual:** it first aborted while loading `DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalGeneralN` because its `.olean` file was absent; retries similarly missed `ResidueResultantTowerSpec`, `RationalIntegrationLiouville`, `IntegratorCases.Defs`, and on 2026-07-22 successively `DeepWiki.CAlgebra.Integrate.LogPartMultiplicity`, `DeepWiki.CAlgebra.IntegrateRisch`, and `Engine.CoupledDE.TangentSpecial`. The named object can already exist immediately after the failure, and queries keep serving the old graph until a later rebuild succeeds.
- **Why it's a limitation:** the full gate did not materialize this aggregator-imported module before the graph loader required it.
- **Workaround used:** explicitly build each reported module and rerun `scripts/wiki build`; sometimes an immediate retry is enough once the object appears.
- **Suggested fix:** have `scripts/wiki build` build missing imported modules before loading the environment, or make the full gate include the complete aggregator closure.
- **Status:** open
