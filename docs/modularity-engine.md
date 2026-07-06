# The modularity analytics engine (quantified refactoring suggestions)

**Status:** Phase 1 built (`scripts/modularity.py`); Phases 2–3 specced · Codex-executable

A decision-support engine that turns WikiRAG's exact `uses` dependency graph (`.wiki/graph.db`) into
**quantified, ranked** refactoring suggestions for an agent — so a novice agent randomly entering the
codebase is handed a *map with confidence scores*, not left to grep. It **suggests and ranks; the agent
validates and acts.** Grounded in software-modularization research (Mancoridis–Mitchell Bunch / the MQ
cohesion-coupling metric; community detection), semantic clone detection (GraphCode2Vec = embeddings +
dependence graph), and ITP premise selection (deep-graph-embedding retrieval, LeanSearch/LeanDojo).

The four concerns it answers:
1. *quantified modularization suggestions* → analyses 1–2 + directory health;
2. *every module understandable to a novice* → Phase 3 cluster summaries + self-containedness;
3. *distant-but-similar → regroup, without over/under-refactoring* → analyses 3–4 + the over/under flags;
4. *similarity / subsumability / unifiability → retire* → analysis 5 (+ Phase 2 semantic precision).

## Phase 1 — structural engine (BUILT)

`python3 scripts/modularity.py [--prefix <namespace>] [--top N] [--json]` reads `.wiki/graph.db` and emits:

| Analysis | Signal | Feeds |
|---|---|---|
| **cohesion/coupling** per module & directory | MQ ratio `intra/(intra+inter)` | health, split |
| **split candidates** | size ≥ 40 ∧ ≥2 internal communities (label propagation on the module's own subgraph) → the *split axis* | `docs/file-splitting-project.md` |
| **misplaced decls** | ≥75% of a decl's `uses`/used-by neighbours live in another module | regroup |
| **co-locate** | module pair with ≥15 cross edges in *different* directories | regroup |
| **duplicate/unifiable** | identical signature-up-to-name, genuine reusable decls (not examples), across modules | `docs/hypothesis-bundling-project.md` + retire |
| **directory health** | flags `under (split)` (max>120 ∧ cohesion<0.55) and `over (merge)` (≥8 modules ∧ avg<6) | over/under calibration |

Real Phase-1 findings on the current tree (validated by hand earlier this project): `GroebnerBasis` → 6
communities; `Computable.Algebraic.RadicalExtension` cohesion **0.14**; `Computable.Tower` cohesion 0.17;
`getD_map_toK`/`radCase3CofactorTower` misplaced into `GenericPolyEngine`; `cderiv/cmonic/cnorm/cneg` and
`cmod/cdiv/cinvMod` re-defined across `LogToAtan`/`RtResultant`/`Subresultant` (retire candidates).

**How an agent uses it:** run before starting `file-splitting`/`bundling`/retire work; take the ranked
candidates as the worklist (the split-axis communities become the leaf files; misplaced decls become
`git mv` targets; duplicate clusters become dedup tasks). Then **validate each** — the engine ranks, it
does not decide.

## Phase 2 — semantic layer (add embedding precision)

Requires embeddings: `scripts/wiki index` (local Ollama; `.wiki/graph.db` currently has 0). Then extend
`modularity.py` with a cosine-similarity pass over the `embedding` BLOBs:
- **precise duplicate/subsumability**: signature-identity (Phase 1) over-flags *same-type, different-meaning*
  decls (worked examples). Embedding cosine distinguishes *same-meaning* (true dedup) from coincidental
  type-equality — the GraphCode2Vec insight (combine embedding **and** graph proximity, neither alone).
- **semantic misplacement / distant-but-similar**: decls whose embedding neighbours cluster in a different
  directory than their graph neighbours = "similar-but-far" regroup candidates (concern 3).
- **subsumption ranking**: for a candidate pair, the more-general one (fewer hypotheses / the other's
  statement is an instance) is the survivor; flag the specific one to retire via the general.

## Phase 3 — novice-comprehension layer

For each detected community, generate an LLM summary ("what this cluster is, its entry points, what it
depends on") and a **self-containedness score** (fraction of a module's deps that are local + whether it
has a module docstring). Surface via a new `scripts/wiki summarize <module>` and store back into a
`summaries` table. This is the "novice randomly enters and isn't lost" layer — the RAG comprehension use.

## Calibration & guardrails (avoid over- and under-refactoring)

- The `over`/`under` directory-health flags are the calibration dial; tune thresholds against the existing
  well-formed areas (e.g. `Compute/` cohesion 0.67 is "ok" — don't touch). A suggestion is only actionable
  if it also *reads* sensibly; **the engine never rewrites** — it emits a worklist an agent vets.
- Re-run `scripts/wiki build` before analysis so the graph is current; the graph is **exact** (from Lean's
  environment), so structural signals are trustworthy; embedding signals (Phase 2) are fuzzy and ranked.
- Do not chase low-confidence suggestions; a duplicate cluster across *intentionally-separate carriers*
  (different `CField`/tower instances) is not a defect. When Phase 1 and a hand-read disagree, trust the
  hand-read and note the false positive to tune thresholds.
