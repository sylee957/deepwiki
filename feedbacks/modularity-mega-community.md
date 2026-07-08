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
- **Workaround used:** replaced the size term with a data-driven **module-scale size prior**
  `size·exp(−size/τ)`, τ = mean module size, so the score peaks at module scale and decays to ~0 for
  the backbone — a continuous score, no hard cutoff. Also excluded compiler-generated decls
  (`casesOn`/`noConfusion`/`rec`/match-proof helpers) that formed a spurious low-cohesion "theme".
- **Suggested fix (deeper):** swap label propagation for a modularity-optimizing community algorithm
  (Louvain/Leiden) for more balanced communities; and fold conceptual + co-change edges *into* the
  clustering (not just the scoring) so mathematically-kin but structurally-thin themes still cluster.
- **Status:** fixed in 65db7211 (size prior + noise filter); Louvain/combined-edge clustering still open.
