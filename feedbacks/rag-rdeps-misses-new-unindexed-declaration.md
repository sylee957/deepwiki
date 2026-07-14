# `wiki rdeps` misses a newly built declaration before graph refresh

- **Date:** 2026-07-14
- **Tool/step:** `scripts/wiki rdeps DeepWiki.Refine.BinaryNat.mul --depth 2 --json`
- **Expected:** The command finds `BinaryNat.mul`, which is present in the current source and has
  already passed a targeted build.
- **Actual:** It returned `no declaration matching DeepWiki.Refine.BinaryNat.mul` while source-level
  `rg` found the declaration and its callers.
- **Why it's a limitation:** The graph database does not distinguish a stale snapshot from a truly
  absent declaration in this result.
- **Workaround used:** Trusted the current source and `rg` results for the impact audit.
- **Suggested fix:** When resolution fails, report the graph build timestamp or suggest
  `scripts/wiki build` before concluding that the declaration does not exist.
- **Status:** open
