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

### Visualizing

`wiki dot` exports a subgraph in several formats, at three scales: a **decl
neighborhood** (`<name>`, with `--depth`, `--rev` for dependents, `--both`), the **module
DAG** (`--modules`, ~170 nodes), and **the entire declaration graph** (`--all`, ~3.2k
nodes / ~16k edges). The full graph is a hairball in 2D — use `--3d`, where it's actually
navigable.

```bash
# Interactive, zero-install (CDN — opens in any browser):
scripts/wiki dot --modules --html > modules.html && open modules.html   # 2D (vis-network)
scripts/wiki dot --modules --3d   > modules3d.html && open modules3d.html # 3D (three.js)
scripts/wiki dot IsMaximalArrivalCurve --both --html > nbr.html && open nbr.html
scripts/wiki dot --all --3d > all.html && open all.html                   # every decl, 3D

# Graphviz (best static quality; brew install graphviz):
scripts/wiki dot --modules | dot -Tsvg -o modules.svg && open modules.svg
scripts/wiki dot DeepWiki.minConv --rev --depth 2 | sfdp -Tsvg -o impact.svg

# Mermaid (paste into Markdown / GitHub / a Mermaid-aware IDE preview):
scripts/wiki dot IsMaximalArrivalCurve --both --mermaid
```

HTML nodes are coloured by kind, carry the full signature on hover, and the focus
node is highlighted; `dot` neighborhoods carry signatures as Graphviz tooltips.
Short names (`minConv`) auto-resolve; ambiguous ones list their candidates.
Re-run `scripts/wiki build` after changing the library — it **preserves embeddings**
for declarations whose name, kind, signature and docstring are unchanged, so only
new/changed decls need a follow-up `scripts/wiki index` (it reports how many).

## Embeddings (optional, local)

```bash
brew install ollama && ollama serve &
ollama pull nomic-embed-text
scripts/wiki index        # embed decls lacking a vector (only fills gaps)
```

Without Ollama, `context` falls back to lexical seeds only; everything else is
unaffected. Configure via env: `WIKI_DB`, `WIKI_OLLAMA_URL`, `WIKI_EMBED_MODEL`.

### State model: migrate / update / switch

The DB carries a `meta` table (`schema_version`, `embed_model`, `embed_dim`) and
maintains one invariant: **every stored embedding came from the single recorded
model** (mixing vector spaces in one column silently corrupts cosine scores). Three
transitions keep it true:

- **migrate** — the schema evolves; applied automatically on open and idempotent. A
  pre-`meta` DB is detected and its existing vectors are back-filled with the model/dim.
- **update** — the library changed: `scripts/wiki build` re-extracts (preserving
  embeddings for unchanged decls), then `scripts/wiki index` embeds the new/changed ones
  *with the same model*. `index` **refuses** if `WIKI_EMBED_MODEL` differs from the
  recorded model.
- **switch** — change the embedding model:
  `WIKI_EMBED_MODEL=<m> scripts/wiki reindex` clears all vectors and re-embeds everything
  with `<m>` — the only safe way to change models.

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
