# Semantic reindexing requires a live Ollama service

- **Date:** 2026-07-14
- **Tool/step:** `scripts/wiki index`
- **Expected:** Reindex the 4,620 declarations reported as changed after rebuilding the graph.
- **Actual:** The command stopped after 51 failures with `Ollama unreachable — 51 failures, 0 done`.
- **Why it's a limitation:** Graph maintenance can run unattended, but semantic-index maintenance has an undocumented live-service prerequisite at the point of use.
- **Workaround used:** Kept the successfully rebuilt exact declaration graph and used source inspection plus lexical search for this turn.
- **Suggested fix:** Have `scripts/wiki index` preflight Ollama once and print the startup command before beginning the embedding batch.
- **Status:** open
