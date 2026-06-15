import SQLite

/-! # WikiRAG core: schema, node metadata, persistence, similarity
On-disk graph of the Lean library: `decls` nodes, `edges` (intra-library
`uses`), and a derived `module_edges` graph. Pure SQLite + IO — no Lean
metaprogramming here (that lives in `WikiRAG.Extract`). -/

namespace WikiRAG
open SQLite

/-- Default on-disk location of the graph database (relative to the repo root). -/
def defaultDbPath : String := ".wiki/graph.db"

/-- The decl columns, in the canonical select order used by `readDecl`. -/
def declCols : String := "name, short, kind, module, line, signature, doc"

/-- Metadata for one declaration node. -/
structure DeclMeta where
  name : String
  short : String
  kind : String
  module : String
  line : Nat
  signature : String
  doc : String
deriving Inhabited

/-- Collapse runs of whitespace (incl. newlines/tabs) into single spaces, trimmed. -/
def squeeze (s : String) : String :=
  let s := (s.replace "\n" " ").replace "\t" " "
  " ".intercalate ((s.splitOn " ").filter (· ≠ ""))

/-- `Foo.Bar.baz` → `Foo/Bar/baz.lean`: display source path from a module name. -/
def moduleToFile (m : String) : String := (m.replace "." "/") ++ ".lean"

/-- `True` iff `sub` (nonempty) occurs as a substring of `s`. -/
def containsStr (s sub : String) : Bool := sub ≠ "" && (s.splitOn sub).length ≥ 2

/-- Open (or create) the SQLite database at `path`. -/
def openDb (path : String) : IO SQLite := SQLite.«open» path

/-- (Re)create all tables, dropping any existing graph. -/
def createTables (db : SQLite) : IO Unit := do
  db.exec "DROP TABLE IF EXISTS decls; DROP TABLE IF EXISTS edges; DROP TABLE IF EXISTS module_edges;"
  db.exec "CREATE TABLE decls (name TEXT PRIMARY KEY, short TEXT, kind TEXT, module TEXT, line INTEGER, signature TEXT, doc TEXT, embedding BLOB);"
  db.exec "CREATE TABLE edges (src TEXT, dst TEXT, PRIMARY KEY(src, dst));"
  db.exec "CREATE INDEX edges_dst ON edges(dst);"
  db.exec "CREATE INDEX decls_short ON decls(short);"
  db.exec "CREATE TABLE module_edges (src TEXT, dst TEXT, weight INTEGER, PRIMARY KEY(src, dst));"

/-- Bulk-insert decl nodes and use-edges, prune dangling/self edges, derive the module graph. -/
def insertGraph (db : SQLite) (metas : Array DeclMeta) (edges : Array (String × String)) : IO Unit := do
  db.transaction do
    let s ← db.prepare "INSERT OR REPLACE INTO decls (name, short, kind, module, line, signature, doc) VALUES (?,?,?,?,?,?,?)"
    for m in metas do
      s.bindText 1 m.name
      s.bindText 2 m.short
      s.bindText 3 m.kind
      s.bindText 4 m.module
      s.bindText 5 (toString m.line)
      s.bindText 6 m.signature
      s.bindText 7 m.doc
      s.exec
      s.reset
      s.clearBindings
  db.transaction do
    let e ← db.prepare "INSERT OR IGNORE INTO edges (src, dst) VALUES (?,?)"
    for (a, b) in edges do
      e.bindText 1 a
      e.bindText 2 b
      e.exec
      e.reset
      e.clearBindings
  db.exec "DELETE FROM edges WHERE src = dst OR src NOT IN (SELECT name FROM decls) OR dst NOT IN (SELECT name FROM decls);"
  db.exec "DELETE FROM module_edges;"
  db.exec "INSERT INTO module_edges (src, dst, weight) SELECT s.module, d.module, COUNT(*) FROM edges e JOIN decls s ON e.src = s.name JOIN decls d ON e.dst = d.name WHERE s.module <> d.module GROUP BY s.module, d.module;"

/-- Cosine similarity of two vectors (0 if either is degenerate). -/
def cosine (a b : Array Float) : Float := Id.run do
  let n := min a.size b.size
  let mut dot := 0.0
  let mut na := 0.0
  let mut nb := 0.0
  for i in [0:n] do
    let x := a[i]!
    let y := b[i]!
    dot := dot + x * y
    na := na + x * x
    nb := nb + y * y
  if na == 0.0 || nb == 0.0 then return 0.0
  return dot / (Float.sqrt na * Float.sqrt nb)

end WikiRAG
