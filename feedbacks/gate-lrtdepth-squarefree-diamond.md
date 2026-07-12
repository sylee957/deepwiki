# LrtDepth.lean committed non-compiling — CPolySquarefree instance diamond

- **Date:** 2026-07-12
- **Tool/step:** scripts/check.sh (full `lake build`)
- **Expected:** HEAD (`c1168833`) gates green; `DeepWiki/SymbolicIntegration/Engine/Tower/LrtDepth.lean`
  (added in `8fb2a712` "Compose transcendental tower stages") compiles.
- **Actual:** `lake build DeepWiki.SymbolicIntegration.Engine.Tower.LrtDepth` fails deterministically —
  it is the **only** failing module in the whole default build. Errors: `whnf`/`isDefEq` heartbeat
  timeouts (lines ~120/238/243, do NOT converge even at 6.4M heartbeats), `failed to synthesize`
  cascades (lines 91/98/112/303/378), and a real type mismatch (line 526). The `.olean` never existed;
  earlier `GATE: PASS` runs were reading a stale cache from before this file compiled cleanly on some
  other machine.
- **Why it's a limitation:** genuine design flaw, not a timeout. Two non-defeq global squarefree
  instances exist — `instCPolySquarefreeDenseWf` (high prio, `= cSqfreeYunFF`) and
  `instCPolySquarefreeDense` (low prio, `= CPolySquarefree.default`) — and `CPolySquarefree` carries a
  data field (not `Subsingleton`). `DenseLrtStage`/`DenseLrtLevelCapabilities` thread the abstract
  `capabilities.squarefree` field through every residue method + the `residueCriterion` structure-field
  type via `letI`, while the underlying LRT lemmas (`cLrtLogArgG_eq_nil_of_cdegG_zero`,
  `cIntegrateReducedLrt`, `primitiveLrtResidueCriterionWf`) resolve a *different* squarefree instance.
  Proving the two giant `cHermiteReduceTower`/`cLrtLogArg` tower terms defeq forces `whnf` to reduce
  them and blows the budget; `rw`/`exact` report "pattern not found" on terms that pretty-print
  identically but differ in a hidden instance arg. Confirmed: with `[CPolySquarefree DensePoly α]` as a
  hypothesis the residue proof fails; with it dropped (uniform global instance) the identical proof
  compiles instantly.
- **Workaround used:** none available for the gate — the file cannot be made to compile by local tactic
  edits. Verified this is orthogonal to the presentation-orchestration migration
  (`Tower/DifferentialLegacyCapabilities.lean`), which builds clean and does not import `LrtDepth`.
- **Suggested fix:** a scoped refactor making the whole `DenseLrtStage` layer use ONE consistent
  squarefree instance — either drop the `capabilities.{squarefree,gcd,splitFactor}` fields in favor of
  the canonical globals across the ~8 residue methods + the `residueCriterion` field type, or thread
  `capabilities.squarefree` down into the LRT lemmas. Three non-controversial prerequisite fixes are
  already root-caused and independently verified: (1) thread `[CFracGcdCoreWf (DenseFracTower n)]` /
  `[CFieldDomain (DenseFracTower n) DensePoly]` as explicit instance args (resolution can't recurse on
  `n`; base instances live only at `ℚ`); (2) `open scoped Classical in` before
  `normalResidueSupport_of_genuineMonomial` (for `NormalizedGCDMonoid`, as `GenuineMonomial.lean` does);
  (3) a `toPoly`-bridge `have` at line 526 (the pattern already at line 482). The
  `allResiduesConstantLrt_of_noPoles` timeout is fixed by `show … = true; unfold allResiduesConstantLrt;
  rw [show (…).logs = cLrtLogArg … from rfl, cLrtLogArgG_eq_nil_of_cdegG_zero …, List.all_nil]` — but
  only once the squarefree instance is uniform.
- **Status:** open
