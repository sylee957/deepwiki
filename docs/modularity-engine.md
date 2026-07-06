# The modularity analytics engine (scored refactoring signals)

**Status:** structural engine built in WikiRAG (`wiki modularity`); semantic layer specced · **Repo:** `deepwiki`

A decision-support engine that turns WikiRAG's exact `uses` dependency graph (`.wiki/graph.db`) into
**quantified, ranked** refactoring signals — so a novice agent entering the codebase gets a *map with
scores*, not a grep. It **scores and ranks; the agent validates and acts.** Grounded in the software
modularization literature (Mancoridis–Mitchell MQ; **Newman modularity `Q`**), semantic clone detection
(GraphCode2Vec = embeddings + dependence graph), and ITP premise selection (deep-graph-embedding retrieval).

**Design principle — every signal is a continuous score, never a hard threshold.** There are no magic
cutoffs (`size > 40`, `frac ≥ 75`, …); each module/decl/pair is *ranked by a score* and the top ones shown.
The only knobs are `--top=N` (display count) and `--prefix=NS` (scope).

## Usage

```bash
scripts/wiki modularity                       # DeepWiki.SymbolicIntegration, top 15
scripts/wiki modularity --prefix=DeepWiki.NetworkCalculus --top=20
```

## The scores (structural; from the graph alone, no embeddings)

| Signal | Score | Meaning |
|---|---|---|
| **split** | internal **Newman modularity `Q`** of the module's own subgraph (label-propagation communities) | high `Q` ⇒ genuine sub-community structure → split; a flat bag scores ~0 (`#communities` = the split axis) |
| **misplacement** | `(bestOtherAffinity − homeAffinity) · (1 − 1/deg)` | a decl pulled toward another module; degree-discounted so low-degree noise self-attenuates (no degree cutoff) |
| **coupling** | `cross(m₁,m₂) / √(size₁·size₂)` | size-normalised cross-*directory* coupling → co-locate/regroup |
| **cohesion / granularity** | `intra / (intra+inter)` per module & directory | reported as numbers, sorted worst-first — over/under-refactoring reads off the distribution, not a boolean flag |

Real output on the current tree (validated by hand earlier): split — `RadicalExtension` `Q=75` (6 comms),
`GcdFF` `Q=70` (10), `ZassenhausDecider` `Q=63` (72 decls, 8); misplacement — `getD_map_toK`,
`radCase3CofactorTower` → `GenericPolyEngine`; coupling — `RadicalIntegralSoundness ⇄ GenericPolyEngine`
(score 599); granularity — `Computable.Tower` cohesion 17%, `RischDE` 18% (low-cohesion dirs).

**How an agent uses it:** run before `file-splitting` / regroup / retire work; take the ranked lists as the
worklist — the split communities become leaf files, high-misplacement decls become `git mv` targets, high
coupling pairs become co-location candidates. Then **validate each**; the engine ranks, it does not decide.

## Semantic layer (specced — the continuous similarity/retire score)

`.wiki/graph.db` currently has **0 embeddings** (`scripts/wiki index` needs a local Ollama). The
**duplicate / subsumability / unifiability** signal is deliberately *not* an exact-signature filter (that
was a deterministic match, and over-flags same-typed worked examples). Its principled form is a **continuous
similarity score** = embedding cosine × structural neighbour-overlap (the GraphCode2Vec insight: combine
graph and embedding, neither alone). Once embeddings exist, add to `Modular.lean`:
- **similarity/retire score** per decl pair: cosine(emb) blended with Jaccard(neighbour sets); rank; the
  more-general decl (fewer hypotheses / the other's statement is an instance) is the survivor.
- **semantic misplacement**: decls whose embedding neighbours cluster in a different directory than their
  graph neighbours = "distant-but-similar" regroup candidates.

## Comprehension layer (specced — for the novice)

Per detected community, an LLM summary ("what this cluster is, entry points, dependencies") + a
self-containedness score (fraction of local deps + presence of a module docstring), surfaced as
`wiki summarize <module>`. This is the "novice enters anywhere and isn't lost" layer.

## Guardrails

- The engine **never rewrites** — it emits scored worklists an agent vets. A high score is a *prior*, not a
  verdict; a duplicate across intentionally-separate carriers (different `CField`/tower instances) is not a
  defect. When a score and a hand-read disagree, trust the hand-read.
- Re-run `scripts/wiki build` before analysis so the graph is current. Structural scores are trustworthy
  (the `uses` graph is exact); the semantic scores (once added) are fuzzy priors, ranked.
