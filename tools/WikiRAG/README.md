# WikiRAG — local graph-RAG over the Lean library

A self-contained, no-daemon graph-RAG index of the DeepWiki Lean library that
Claude Code (or you) drive from the CLI. **The graph is exact**, extracted from
Lean's own environment — not approximated by embeddings.

## What it indexes

A `lake exe` (`wiki`) imports the compiled `DeepWiki` + `Sources` environment and
walks every declaration into a single SQLite file (`.wiki/graph.db`, gitignored):

- **Nodes** (`decls`): name, kind, module, line, pretty-printed signature, docstring.
- **Edges** (`edges`): the intra-library `uses` relation — `A → B` iff `A`'s type
  or proof term references `B` (`ConstantInfo.getUsedConstantsAsSet`).
- **Module graph** (`module_edges`): the `uses` relation projected onto modules.
- **Embeddings** (`embedding` BLOB): optional per-decl vector from a local Ollama
  server, stored as an `Array Float` BLOB.

## Why this shape (not flat doc-embedding RAG)

A Lean environment *is* a typed dependency graph. Retrieval here is
**lexical-first, graph-expand**: precise identifier/docstring matching finds seed
declarations, then `deps`/`rdeps` traversal pulls in the proof context that
actually matters when reading or editing a theorem ("what does this build on",
"what breaks if I change it"). Embeddings add fuzzy-synonym recall on top.

At ~3,100 nodes / ~16k edges the corpus is tiny, so graph traversal runs as SQLite
recursive CTEs and vector KNN is brute-force cosine in Lean — no `sqlite-vec`/FTS5,
no graph DB server. The embedding column is pluggable if the wiki ever outgrows this.

## Usage

```bash
lake build wiki          # one-time: build the exe
scripts/wiki build       # extract the graph (~20s; reloads the whole env)

scripts/wiki search "maximal arrival curve" -k 5
scripts/wiki show IsMaximalArrivalCurve            # sig + doc + uses/used-by
scripts/wiki deps  IsMaximalArrivalCurve --depth 2 # what it builds on
scripts/wiki rdeps DeepWiki.minConv --depth 1      # impact set
scripts/wiki path  IsMaximalArrivalCurve DeepWiki.minConv
scripts/wiki context "residual service curve"      # seeds + neighborhood bundle
```

Add `--json` to `search`/`show`/`deps`/`rdeps` for machine-readable output.
Short names (`minConv`) auto-resolve; ambiguous ones list their candidates.
Re-run `scripts/wiki build` after changing the library.

## Embeddings (optional, local)

```bash
brew install ollama && ollama serve &
ollama pull nomic-embed-text
scripts/wiki index        # embeds every decl; safe to re-run (only fills gaps)
```

Without Ollama, `context` falls back to lexical seeds only; everything else is
unaffected. Configure via env: `WIKI_DB`, `WIKI_OLLAMA_URL`, `WIKI_EMBED_MODEL`.

## Layout

| File | Role |
|---|---|
| `Basic.lean`   | schema, persistence, cosine, string utils |
| `Extract.lean` | environment walk → nodes + edges (Lean metaprogramming) |
| `Embed.lean`   | Ollama embeddings + indexing |
| `Query.lean`   | lexical / vector / graph queries |
| `Main.lean`    | CLI dispatch |

Built via the `WikiRAG` lib + `wiki` exe in `lakefile.toml`, both kept **out of
`defaultTargets`** so the warning-/sorry-free `lake build` gate over the math
library is untouched.
