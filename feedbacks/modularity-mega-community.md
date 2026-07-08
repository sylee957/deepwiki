# `modularity` communities collapse into a mega-community on the dense uses graph

- **Date:** 2026-07-08
- **Tool/step:** `scripts/wiki modularity` — the COMMUNITIES partition-diff
- **Expected:** label propagation over the `uses` graph yields module-sized communities, so a
  community spanning many directories reads as a "scattered theme to regroup."
- **Actual:** on the densely-connected engine graph, label propagation collapses most of the graph
  into 1–2 giant communities (e.g. 1645 decls spanning 9 directories). Ranking scattered themes by
  `(dirs−1)·cohesion·√size` then promoted exactly that backbone blob to the top — un-actionable (you
  can't lift the whole library into one module).
- **Why it's a limitation:** raw label propagation under-segments dense graphs; and a raw size term
  in the score rewards the backbone rather than *liftable* module-sized clusters.
- **Workaround (first pass):** replaced the size term with a data-driven **module-scale size prior**
  `size·exp(−size/τ)`, τ = mean module size, so the score peaks at module scale and decays to ~0 for
  the backbone — a continuous score, no hard cutoff. Also excluded compiler-generated decls
  (`casesOn`/`noConfusion`/`rec`/match-proof helpers) that formed a spurious low-cohesion "theme".
- **Deeper fix (done):** replaced label propagation with **weighted Louvain** single-level
  local-moving. Its modularity-gain criterion `kᵢ,in(c) − Σtot(c)·kᵢ/2m` penalises merging into an
  already-large community, so the giant-community collapse is gone (largest community 1645 → ~30
  decls, balanced and module-sized). Kept single-level *by design* — Louvain's aggregation phase
  coarsens communities, the opposite of what surfacing liftable themes needs. And folded conceptual +
  co-change signals *into the clustering* (not just the score): each `uses` edge is reinforced by
  `wcon`·docstring-cosine + `wevo`·co-change (weights, not thresholds; CLI `--wcon=`/`--wevo=`), so
  conceptually-kin but structurally-thin themes now cluster (visible: top communities at con 84–94%).
- **Status:** fixed — size prior + noise filter in 65db7211; weighted Louvain + combined-edge
  clustering in the follow-up commit. Remaining ideas (low priority): Leiden (Louvain's refinement
  guaranteeing connected communities), and conceptual kNN edges between structurally-disconnected
  decls (currently concept only reinforces existing `uses` edges, an O(edges) design that avoids the
  O(n²) all-pairs cosine).
