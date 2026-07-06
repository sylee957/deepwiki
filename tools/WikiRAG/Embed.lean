import Lean
import WikiRAG.Basic

/-! # WikiRAG embeddings: local semantic vectors via Ollama
Shells out to a local Ollama server for embeddings and stores them as
`Array Float` BLOBs (leansqlite's `ToBinary`). Degrades gracefully when
Ollama is unreachable: the graph + lexical search work without it. -/

namespace WikiRAG
open SQLite SQLite.Blob Lean

/-- Ollama base URL (`WIKI_OLLAMA_URL`, default `http://localhost:11434`). -/
def ollamaUrl : IO String := return (← IO.getEnv "WIKI_OLLAMA_URL").getD "http://localhost:11434"

/-- Embedding model (`WIKI_EMBED_MODEL`, default `nomic-embed-text`). -/
def embedModel : IO String := return (← IO.getEnv "WIKI_EMBED_MODEL").getD "nomic-embed-text"

/-- Request an embedding from a local Ollama server; `none` if unreachable/unparsable. -/
def embedText (text : String) : IO (Option (Array Float)) := do
  let url ← ollamaUrl
  let model ← embedModel
  let body := (Json.mkObj [("model", Json.str model), ("prompt", Json.str text)]).compress
  let out ← IO.Process.output
    { cmd := "curl", args := #["-s", "--max-time", "120", s!"{url}/api/embeddings", "-d", body] }
  if out.exitCode != 0 then return none
  match Json.parse out.stdout with
  | .error _ => return none
  | .ok j =>
    match j.getObjVal? "embedding" with
    | .error _ => return none
    | .ok e =>
      match e.getArr? with
      | .error _ => return none
      | .ok arr =>
        let vec := arr.filterMap (fun x => (x.getNum?.toOption).map (·.toFloat))
        if vec.isEmpty then return none else return some vec

/-- Embedding text for a declaration: kind, short name, signature, docstring. -/
def embedDoc (short kind sig doc : String) : String := s!"{kind} {short}\n{sig}\n{doc}"

/-- Dimension of the stored embeddings, read from any one BLOB (`none` if there are none). -/
def sampleEmbedDim (db : SQLite) : IO (Option Nat) := do
  let s ← db.prepare "SELECT embedding FROM decls WHERE embedding IS NOT NULL LIMIT 1"
  if (← s.step) then
    match (fromBinary (← s.columnBlob 0) : Except String (Array Float)) with
    | .ok v => return some v.size
    | .error _ => return none
  else return none

/-- Apply schema migrations on open. v1→v2 adds the `meta` table and records the model +
dimension behind any pre-existing embeddings (assumed produced by the configured model).
Idempotent; safe to call on every command. -/
def migrate (db : SQLite) : IO Unit := do
  ensureMeta db
  let stored := ((← getMeta db "schema_version").bind String.toNat?).getD 0
  let hasDecls ← (do
    let s ← db.prepare "SELECT 1 FROM sqlite_master WHERE type='table' AND name='decls'"
    s.step)
  -- A pre-`meta` DB that already holds nodes is schema v1.
  let stored := if stored == 0 && hasDecls then 1 else stored
  if stored < schemaVersion then
    if hasDecls then
      let nEmb ← countWhere db "SELECT COUNT(*) FROM decls WHERE embedding IS NOT NULL"
      if nEmb > 0 && (← getMeta db "embed_model").isNone then
        setMeta db "embed_model" (← embedModel)
        match (← sampleEmbedDim db) with
        | some d => setMeta db "embed_dim" (toString d)
        | none => pure ()
    setMeta db "schema_version" (toString schemaVersion)

/-- Embed every decl lacking a vector, **with the configured model**. Refuses to run if the
DB already holds embeddings from a *different* model (would mix vector spaces) — use
`reindexAll` to switch. Records the model + dimension on the first success. Stops if Ollama
is unreachable. -/
def indexAll (db : SQLite) : IO Unit := do
  ensureMeta db
  let current ← embedModel
  let nEmb ← countWhere db "SELECT COUNT(*) FROM decls WHERE embedding IS NOT NULL"
  if nEmb > 0 then
    match (← getMeta db "embed_model") with
    | some m =>
      if m ≠ current then
        IO.eprintln s!"Model mismatch: this DB was embedded with `{m}`, but \
          WIKI_EMBED_MODEL=`{current}`. Vectors from different models share one column and \
          must not be mixed. Run `scripts/wiki reindex` to switch (clears + re-embeds all), \
          or unset WIKI_EMBED_MODEL."
        return
    | none => pure ()
  let sel ← db.prepare "SELECT name, short, kind, signature, doc FROM decls WHERE embedding IS NULL"
  let mut rows : Array (String × String × String × String × String) := #[]
  while (← sel.step) do
    rows := rows.push (← sel.columnText 0, ← sel.columnText 1, ← sel.columnText 2,
      ← sel.columnText 3, ← sel.columnText 4)
  if rows.isEmpty then
    IO.println "All declarations already embedded (nothing to do)."
    return
  IO.println s!"Embedding {rows.size} declarations via Ollama ({current})…"
  let mut done := 0
  let mut failed := 0
  let mut consec := 0     -- consecutive failures; a long streak ⇒ Ollama is actually down
  for (name, short, kind, sig, doc) in rows do
    let txt := embedDoc short kind sig doc
    -- one retry smooths transient failures (e.g. a cold model reload)
    let ev ← (do match (← embedText txt) with | some v => pure (some v) | none => embedText txt)
    match ev with
    | none =>
      failed := failed + 1; consec := consec + 1
      if consec > 50 then
        IO.eprintln s!"Ollama unreachable — {failed} failures, {done} done. Aborting; \
          run `ollama serve` (+ `ollama pull {current}`) and re-run to resume."
        return
    | some vec =>
      consec := 0
      if done == 0 && (← getMeta db "embed_model").isNone then
        setMeta db "embed_model" current
        setMeta db "embed_dim" (toString vec.size)
      let upd ← db.prepare "UPDATE decls SET embedding = ? WHERE name = ?"
      upd.bindBlob 1 (toBinary vec)
      upd.bindText 2 name
      upd.exec
      done := done + 1
      if done % 100 == 0 then IO.println s!"  …{done}/{rows.size} ({failed} skipped)"
  IO.println s!"Indexed {done} embeddings ({failed} skipped — re-run to retry them). \
    Model `{current}`, dim {(← getMeta db "embed_dim").getD "?"}."

/-- Model *switch*: drop all embeddings and re-embed everything with the configured model. -/
def reindexAll (db : SQLite) : IO Unit := do
  let current ← embedModel
  let n ← countWhere db "SELECT COUNT(*) FROM decls WHERE embedding IS NOT NULL"
  IO.println s!"Switching embedding model → `{current}`: clearing {n} embedding(s), re-embedding all…"
  clearEmbeddings db
  indexAll db

end WikiRAG
