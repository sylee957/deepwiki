# The `DeepWiki` lib globs — an un-imported module still passes the gate (false coherence)

**Date:** 2026-07-09

**Friction.** I added four new modules under `DeepWiki/ComputableAlgebra/` (`PolyEngine`,
`PolyReprDivision`, `PolyReprDivisionDegree`, `PolyReprResultant`) and tried to wire each into the
`DeepWiki/ComputableAlgebra.lean` aggregator with `sed 's|import …anchor|…|'`. The `sed` anchor
didn't match (an earlier `7a\` insertion had silently failed), so **none** of the four imports
actually landed in the aggregator — yet `scripts/check.sh` reported `GATE: PASS` every time, and
`lake build DeepWiki.ComputableAlgebra.<Mod>` built each module fine.

**Why it's misleading.** Unlike the `Sources` lib (documented in `CLAUDE.md` as *no globs* — an
un-imported catalog is silently skipped by the gate), the **`DeepWiki` lib globs its files**, so a
new module compiles and is gate-covered *even when no aggregator imports it*. The gate passing
therefore does **not** prove the module is reachable through the aggregator's import chain — which
is what doc-gen and downstream `import DeepWiki.ComputableAlgebra` actually rely on. This is the
mirror image of the `Sources` ORPHAN check: there an un-imported module is *invisible* to the gate;
here it is *built but disconnected*, giving false confidence that the aggregator is complete.

**What to do.**
- Don't trust `sed`-into-aggregator to have worked — **verify** with
  `grep -E "PolyRepr|PolyEngine" DeepWiki/ComputableAlgebra.lean` (or read the file) after adding a
  module, the same discipline as the `Sources` ORPHAN audit.
- A cheap aggregator-completeness audit for a globbed dir:
  `for f in DeepWiki/ComputableAlgebra/*.lean; do m=$(basename $f .lean); grep -q "import DeepWiki.ComputableAlgebra.$m\b" DeepWiki/ComputableAlgebra.lean || echo "NOT-IN-AGGREGATOR $m"; done`
  (skips the aggregator itself).
- Prefer an `Edit` on the aggregator over `sed` for import insertion — the exact-match failure mode
  of `Edit` is loud, `sed`'s is silent.
