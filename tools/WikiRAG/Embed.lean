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

/-- Compute and store embeddings for every decl lacking one; stops early if Ollama is down. -/
def indexAll (db : SQLite) : IO Unit := do
  let sel ← db.prepare "SELECT name, short, kind, signature, doc FROM decls WHERE embedding IS NULL"
  let mut rows : Array (String × String × String × String × String) := #[]
  while (← sel.step) do
    rows := rows.push (← sel.columnText 0, ← sel.columnText 1, ← sel.columnText 2,
      ← sel.columnText 3, ← sel.columnText 4)
  if rows.isEmpty then
    IO.println "All declarations already embedded (nothing to do)."
    return
  IO.println s!"Embedding {rows.size} declarations via Ollama ({← embedModel})…"
  let mut done := 0
  for (name, short, kind, sig, doc) in rows do
    match (← embedText (embedDoc short kind sig doc)) with
    | none =>
      IO.eprintln s!"Ollama unreachable or empty embedding after {done} done. \
        Run `ollama serve` and `ollama pull {← embedModel}`, then re-run `wiki index`."
      return
    | some vec =>
      let upd ← db.prepare "UPDATE decls SET embedding = ? WHERE name = ?"
      upd.bindBlob 1 (toBinary vec)
      upd.bindText 2 name
      upd.exec
      done := done + 1
      if done % 100 == 0 then IO.println s!"  …{done}/{rows.size}"
  IO.println s!"Indexed {done} embeddings."

end WikiRAG
