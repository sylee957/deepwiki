# feedbacks/ — a running log of tooling & workflow friction

When an AI agent (or a human) hits a **limitation of the RAG tooling** (`scripts/wiki`) or a
**workflow friction** (the gate, doc-gen, the migration loop, a convention that fights the task)
that made something *weird, wrong, or harder than it should be* — write it down here. This is the
place the tools themselves get better: a friction that is only felt and never recorded gets
re-hit by the next agent.

This is **not** for math adjudications or coverage status (those go to memory and the `Sources/`
catalogs). It is for *the tools and the process*: "the RAG said X but the truth was Y", "the
loop's signal pointed the wrong way", "the gate/doc-gen behaved surprisingly".

## When to add a note

Add one whenever you notice any of:

- **RAG blind spot** — `wiki search`/`context`/`show`/`deps`/`rdeps`/`modularity` returned
  something misleading, missed something a human would find, or a signal (e.g. a `modularity`
  score, a community, the `(str,con,evo,dis)` vector) pointed you at the wrong change.
- **Stale / lossy index** — embeddings or the graph were out of date and you only found out the
  hard way; a decl was invisible because it wasn't indexed; co-change data was empty.
- **Workflow friction** — the gate flagged something confusingly, doc-gen replayed stale HTML, a
  `git mv` reorg needed a step the loop doc didn't mention, a convention in `CLAUDE.md` made the
  natural change awkward.
- **A "why is this weird" moment** — anything where you paused because a tool or process surprised
  you. If it surprised you, it will surprise the next agent.

Don't self-censor: a two-line note about a small friction is worth writing. Over-recording is
cheap; a silently re-hit limitation is not.

## Format

One markdown file per issue (or extend an existing one if it's the same root cause). Name it
`<area>-<short-slug>.md` — e.g. `rag-context-misses-notation.md`, `modularity-mega-community.md`,
`gate-docgen-replay-stale.md`. Keep it short and concrete:

```markdown
# <one-line title>

- **Date:** 2026-07-08
- **Tool/step:** scripts/wiki context  |  scripts/check.sh  |  migration-loop step 3  | …
- **Expected:** what a reasonable agent would expect the tool/step to do.
- **Actual:** what it actually did (paste the command + the surprising output).
- **Why it's a limitation:** the root cause, as far as you can tell.
- **Workaround used:** what you did instead this time.
- **Suggested fix:** a concrete change to the tool / doc / convention (if you have one).
- **Status:** open | fixed in <commit> | wontfix (<reason>)
```

## Closing a note

When a limitation gets fixed (the tool changes, the doc is updated, the convention is revised),
set `Status: fixed in <commit>` in the note rather than deleting it — the history of *why* a tool
works the way it does is useful. Prune only genuine duplicates.
