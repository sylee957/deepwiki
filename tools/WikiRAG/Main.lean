import Lean
import WikiRAG.Basic
import WikiRAG.Extract
import WikiRAG.Embed
import WikiRAG.Query
import WikiRAG.Viz
import WikiRAG.Cochange
import WikiRAG.Modular

/-! # `wiki` — graph-RAG CLI over the Lean library
Subcommands: `build` (extract the graph), `index` (Ollama embeddings),
`search`, `show`, `deps`, `rdeps`, `path`, `context`, `modularity`. All read
commands emit human-readable text, or JSON with `--json`. -/

open Lean WikiRAG SQLite

/-- Database path (`WIKI_DB`, default `.wiki/graph.db`). -/
def dbPathFromEnv : IO String := return (← IO.getEnv "WIKI_DB").getD WikiRAG.defaultDbPath

/-- Open the graph DB (applying schema migrations), erroring if it has not been built yet. -/
def openExisting : IO SQLite := do
  let path ← dbPathFromEnv
  if !(← System.FilePath.pathExists path) then
    throw (IO.userError s!"no graph at {path}; run `wiki build` first")
  let db ← openDb path
  migrate db
  return db

/-- Truncate to `n` chars with an ellipsis. -/
def truncate (s : String) (n : Nat) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ "…"

/-- One-line summary of a hit. -/
def fmtOneLine (h : Hit) : String :=
  s!"{h.kind} {h.name}  [{moduleToFile h.module}:{h.line}]"

/-- Full detail of a hit (kind, location, signature, doc). -/
def fmtDetail (h : Hit) : String :=
  let docPart := if h.doc == "" then "" else s!"\n  {h.doc}"
  s!"{h.kind} {h.name}\n  {moduleToFile h.module}:{h.line}\n  : {h.signature}{docPart}"

/-- JSON object for a hit. -/
def hitJson (h : Hit) : Json :=
  Json.mkObj [("name", toJson h.name), ("kind", toJson h.kind),
    ("module", toJson h.module), ("file", toJson (moduleToFile h.module)),
    ("line", toJson h.line), ("signature", toJson h.signature), ("doc", toJson h.doc)]

/-- Parsed CLI options: positional args plus `-k`, `--depth`, `--json`. -/
structure Opts where
  pos : Array String := #[]
  k : Nat := 8
  depth : Nat := 2
  json : Bool := false

/-- Parse flags out of an argument list. -/
partial def parseOpts (args : List String) (o : Opts) : Opts :=
  match args with
  | [] => o
  | "-k" :: v :: rest => parseOpts rest { o with k := v.toNat?.getD o.k }
  | "--depth" :: v :: rest => parseOpts rest { o with depth := v.toNat?.getD o.depth }
  | "--json" :: rest => parseOpts rest { o with json := true }
  | a :: rest => parseOpts rest { o with pos := o.pos.push a }

/-- The positional args joined into a single query string. -/
def Opts.query (o : Opts) : String := " ".intercalate o.pos.toList

def usage : String := String.intercalate "\n"
  [ "wiki — graph-RAG over the Lean library"
  , ""
  , "  wiki build                 (re)extract the declaration graph into the DB"
  , "  wiki index                 embed decls lacking a vector (same model)"
  , "  wiki reindex               switch embedding model: clear all + re-embed"
  , "  wiki search <query> [-k N] [--json]"
  , "  wiki show <name> [--json]"
  , "  wiki deps <name> [--depth D] [--json]    what <name> uses (transitively)"
  , "  wiki rdeps <name> [--depth D] [--json]   what uses <name> (impact set)"
  , "  wiki path <a> <b>                        a shortest uses-path a → b"
  , "  wiki context <query> [-k N] [--depth D]  seeds + neighborhood bundle"
  , "  wiki dot <name> [--depth D] [--rev|--both] [--mermaid|--html|--3d]  graph a neighborhood"
  , "  wiki dot --modules [--html|--3d]         graph the module dependency DAG"
  , "  wiki dot --all [--html|--3d]             graph every declaration (~3k nodes; use --3d)"
  , ""
  , "Env: WIKI_DB, WIKI_OLLAMA_URL, WIKI_EMBED_MODEL" ]

/-- Resolve a name argument to a single decl, printing disambiguation/erroring as needed. -/
def resolveOne (db : SQLite) (arg : String) : IO (Option Hit) := do
  let names ← resolveName db arg
  match names.toList with
  | [] => IO.println s!"no declaration matching `{arg}`."; return none
  | [n] => getDecl db n
  | many =>
    IO.println s!"`{arg}` is ambiguous; candidates:"
    for n in many do IO.println s!"  {n}"
    return none

unsafe def buildCmd : IO Unit := do
  let dbPath ← dbPathFromEnv
  if let some dir := (System.FilePath.mk dbPath).parent then
    IO.FS.createDirAll dir
  IO.println "Loading environment (DeepWiki + Sources)…"
  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution
  withImportModules #[{module := `DeepWiki}, {module := `Sources}] {} (trustLevel := 1024) fun env => do
    let db ← openDb dbPath
    migrate db
    let coreCtx : Core.Context := { fileName := "<wiki>", fileMap := default }
    let coreState : Core.State := { env := env }
    IO.println "Walking declarations…"
    let ((metas, edges), _) ← Core.CoreM.toIO gather.run' (ctx := coreCtx) (s := coreState)
    IO.println s!"  {metas.size} declarations, {edges.size} raw use-edges."
    buildGraph db metas edges
    let nTot ← countWhere db "SELECT COUNT(*) FROM decls"
    let nEmb ← countWhere db "SELECT COUNT(*) FROM decls WHERE embedding IS NOT NULL"
    IO.println s!"Wrote graph to {dbPath}: {nTot} decls, {nEmb} embeddings preserved, {nTot - nEmb} to (re)index."

def indexCmd : IO Unit := do indexAll (← openExisting)

def reindexCmd : IO Unit := do reindexAll (← openExisting)

def searchCmd (o : Opts) : IO Unit := do
  if o.query == "" then IO.eprintln "usage: wiki search <query> [-k N] [--json]"; return
  let db ← openExisting
  let hits ← lexicalSearch db o.query o.k
  if o.json then
    IO.println (Json.arr (hits.map (fun (_, h) => hitJson h))).pretty
  else if hits.isEmpty then IO.println "no matches."
  else for (_, h) in hits do
    IO.println (fmtOneLine h)
    if h.doc ≠ "" then IO.println s!"    {truncate h.doc 140}"

def showCmd (o : Opts) : IO Unit := do
  if o.query == "" then IO.eprintln "usage: wiki show <name> [--json]"; return
  let db ← openExisting
  match (← resolveOne db o.query) with
  | none => pure ()
  | some h =>
    if o.json then IO.println (hitJson h).pretty
    else
      IO.println (fmtDetail h)
      let uses ← transitive db h.name 1 false
      let usedBy ← transitive db h.name 1 true
      IO.println s!"\n  uses ({uses.size}): {", ".intercalate ((uses.map (·.2.short)).toList)}"
      IO.println s!"  used by ({usedBy.size}): {", ".intercalate ((usedBy.map (·.2.short)).toList)}"

def depsCmd (o : Opts) (reverse : Bool) : IO Unit := do
  if o.query == "" then IO.eprintln "usage: wiki deps/rdeps <name> [--depth D] [--json]"; return
  let db ← openExisting
  match (← resolveOne db o.query) with
  | none => pure ()
  | some h =>
    let rows ← transitive db h.name o.depth reverse
    if o.json then
      IO.println (Json.arr (rows.map (fun (d, x) =>
        Json.mkObj [("depth", toJson d), ("decl", hitJson x)]))).pretty
    else
      let label := if reverse then "used by" else "uses"
      IO.println s!"{h.name} {label} ({rows.size}, depth ≤ {o.depth}):"
      for (d, x) in rows do
        IO.println s!"  [{d}] {fmtOneLine x}"

def dotCmd (rest : List String) : IO Unit := do
  let o := parseOpts rest {}
  let html := o.pos.contains "--html"
  let three := o.pos.contains "--3d"
  let mermaid := o.pos.contains "--mermaid"
  -- Render decl nodes + (pre-filtered) edges in the chosen format.
  let emit := fun (root : String) (nodes : Array Hit) (edges : Array (String × String)) =>
    if three then neighborhood3d root nodes edges
    else if html then neighborhoodHtml root nodes edges
    else if mermaid then neighborhoodMermaid root nodes edges
    else neighborhoodDot root nodes edges
  let db ← openExisting
  if o.pos.contains "--modules" then
    let nodes ← moduleNodes db
    let edges ← moduleGraph db
    IO.println <|
      if three then module3d nodes edges
      else if html then moduleHtml nodes edges
      else moduleDot nodes edges
    return
  if o.pos.contains "--all" then
    let nodes ← allDecls db
    let edges ← allEdges db   -- already pruned to decls in `build`, so every edge is valid
    IO.eprintln s!"Full graph: {nodes.size} nodes, {edges.size} edges — prefer --3d (2D/DOT are heavy at this size)."
    IO.println (emit "" nodes edges)
    return
  let some name := (o.pos.filter (fun a => ! a.startsWith "-")).toList.head? | do
    IO.eprintln "usage: wiki dot <name> [--depth D] [--rev|--both] [--mermaid|--html|--3d]   |   wiki dot --modules|--all [--html|--3d]"
    return
  match (← resolveOne db name) with
  | none => pure ()
  | some h =>
    let rev := o.pos.contains "--rev"
    let both := o.pos.contains "--both"
    let nodes ← neighborhood db h.name o.depth (!rev || both) (rev || both)
    let nodeNames := nodes.map (·.name)
    let edges := (← allEdges db).filter (fun (a, b) => nodeNames.contains a && nodeNames.contains b)
    IO.println (emit h.name nodes edges)

def pathCmd (a b : String) : IO Unit := do
  let db ← openExisting
  let some ha ← resolveOne db a | pure ()
  let some hb ← resolveOne db b | pure ()
  match (← findPath db ha.name hb.name) with
  | some p => IO.println p
  | none => IO.println s!"no uses-path from {ha.name} to {hb.name} (within depth bound)."

def contextCmd (o : Opts) : IO Unit := do
  if o.query == "" then IO.eprintln "usage: wiki context <query> [-k N] [--depth D]"; return
  let db ← openExisting
  let lex ← lexicalSearch db o.query o.k
  let vec ← (do match (← embedText o.query) with
    | none => pure #[]
    | some qv => vectorSearch db qv o.k)
  -- Union seeds (lexical first, then any new vector hits), preserving order.
  let mut seenNames : Array String := #[]
  let mut seeds : Array Hit := #[]
  for (_, h) in (lex ++ vec) do
    unless seenNames.contains h.name do
      seenNames := seenNames.push h.name
      seeds := seeds.push h
  IO.println s!"# Context for: {o.query}\n"
  IO.println s!"## Seeds ({seeds.size})\n"
  for h in seeds do IO.println s!"- {fmtDetail h}\n"
  -- Neighborhood: immediate uses + used-by of each seed, deduped against seeds.
  IO.println "## Neighborhood\n"
  for h in seeds do
    let uses ← transitive db h.name o.depth false
    let usedBy ← transitive db h.name 1 true
    let fmtN (rows : Array (Nat × Hit)) : String :=
      ", ".intercalate ((rows.filterMap (fun (_, x) =>
        if seenNames.contains x.name then none else some x.short)).toList)
    IO.println s!"- {h.short} → uses: {fmtN uses}"
    IO.println s!"  {h.short} ← used by: {fmtN usedBy}"

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println usage
  | "build" :: _ => buildCmd
  | "index" :: _ => indexCmd
  | "reindex" :: _ => reindexCmd
  | "search" :: rest => searchCmd (parseOpts rest {})
  | "show" :: rest => showCmd (parseOpts rest {})
  | "deps" :: rest => depsCmd (parseOpts rest {}) false
  | "rdeps" :: rest => depsCmd (parseOpts rest {}) true
  | "path" :: a :: b :: _ => pathCmd a b
  | "context" :: rest => contextCmd (parseOpts rest {})
  | "cochange" :: _ => do mineCochange (← openExisting)
  | "modularity" :: rest => modularityCmd rest
  | "dot" :: rest => dotCmd rest
  | cmd :: _ => do IO.eprintln s!"unknown command: {cmd}\n"; IO.println usage
