# The recommendation engine (`wiki recommend`)

**Status:** built in WikiRAG (`tools/WikiRAG/Modular.lean`, `scripts/wiki recommend`) · **Repo:** `deepwiki`

Turns WikiRAG's exact `uses` dependency graph (`.wiki/graph.db`), the Ollama docstring embeddings, and
git co-change history into **one concrete, Codex-ready refactoring action** per call. It **scores, ranks,
and samples; the agent validates and acts** — a decision-support engine, not an oracle.

## The three signals it fuses

| Signal | Source | Measures |
|---|---|---|
| **structural** | the `uses` graph (`ConstantInfo.getUsedConstantsAsSet`) | who depends on whom — cohesion, affinity, community structure |
| **conceptual** | Ollama docstring embeddings (per-decl + module centroids) | what *reads alike* — semantic similarity even without a call edge |
| **evolutionary** | git history (`Cochange.lean`, `git log --name-only`) | what *changes together* — Gall/Zimmermann logical coupling |

These are **fused into the clustering**: each `uses` edge is weighted `1 + wcon·docstring-cosine +
wevo·co-change`, then **weighted Louvain** (single-level local-moving, modularity-gain criterion —
resists the giant-community collapse of label propagation) partitions the whole in-scope graph.
Compiler-generated decls (recursors, `noConfusion`, match helpers) are filtered out first.

## The six action types (each a Pareto front over its own objectives)

| Action | When | Objectives (↑ maximise, ↓ cost) |
|---|---|---|
| **regroup-theme** | a community spanning ≥2 directories = a scattered theme | dispersion↑ · cohesion↑ · concept↑ · module-scale-fit↑ |
| **split-dir** | a directory fractured across many communities = a grab-bag | purity↓ · size↑ |
| **merge** | a thin module whose `uses` concentrate on one neighbour | absorb-need↑ · smallness↑ · concentration↑ · concept↑ |
| **move-decl** | a declaration whose deps favour another module | structural-pull↑ · concept↑ · co-change↑ · disturbance↓ |
| **rename-unify** | two name-tokens with near-identical decl centroids = synonyms | centroid-cosine↑ · freq↑ · spelling-sim↑ · co-occurrence↓ |
| **rename-disambiguate** | a token whose decls split into ≥2 embedding clusters = overloaded | dispersion↑ · freq↑ |

The first four are structural (regroup/split answer *what modules should exist*; merge/move are local);
the last two are the **vocabulary/naming** layer. Together they correct over- *and* under-refactoring.

## Design principles

- **Pareto, never weighting.** Within each action type, `paretoFront` keeps the non-dominated candidates
  (weakly-better-on-all, strictly-on-one) — no scalar score, no cutoff. Fronts are *not* compared across
  types (a split is not an alternative to a merge); each keeps its own front.
- **Randomization is the principled selector.** Since within a front nothing dominates, the engine
  **stratified-samples** `--k` action(s) — a bucket (action type), then a member — so the loop rotates
  across action types instead of hammering one. `--seed=N` (the loop passes a fresh seed) makes any run
  reproducible; sampling uses the LCG's high bits (its low bits have a short period).
- **Vocabulary analysis is model-driven — zero hardcoded English.** A name-token is only a grouping key
  (mechanical camelCase split); all same-vs-different judgment comes from the embeddings. Naming particles
  (`eq`/`of`/`to`) are removed by **specificity** (centroid distance from the corpus mean — the geometric
  analogue of a stopword list, `--vspec`), not a word list. Synonyms-vs-collocates is separated by name
  **co-occurrence** (a cost). *Honest limit:* distributional embeddings conflate synonymy with topical
  relatedness (`buchberger`≈`groebner` is real; `dependent`≈`wronskian` is merely related), so unify is a
  *candidate generator* — the card asks Codex to verify same-concept-vs-related and skip if related.

## Usage

```bash
scripts/wiki recommend --prefix=DeepWiki.SymbolicIntegration --seed=$RANDOM   # one action card
scripts/wiki recommend --prefix=… --k=15                                     # a slate to scout
```
Knobs: `--prefix=NS`, `--k=N`, `--seed=N`, clustering weights `--wcon=`/`--wevo=`, vocab `--vmin=`/`--vspec=`
— all weights and sampling, never cutoffs. Needs `scripts/wiki index` for the conceptual/vocab layer;
without embeddings only the four structural types fire.

## Research grounding

Software remodularization (Mancoridis–Mitchell **MQ/Bunch**; Praditwong–Harman–Yao multi-objective module
clustering); community detection (**Newman `Q`**, Louvain/Blondel, Leiden); structural + conceptual
coupling (Bavota et al.); semantic clustering (Kuhn–Ducasse–Gîrba); evolutionary coupling (Gall,
Zimmermann); and, for the naming layer, **Deißenböck–Pizka** concise-and-consistent naming (conciseness =
unify, consistency = disambiguate) and Høst–Østvold's programmer's lexicon.
