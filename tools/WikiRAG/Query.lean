import WikiRAG.Basic
import WikiRAG.Embed

/-! # WikiRAG queries: lexical, vector, and graph traversal
Read-side of the wiki. Lexical ranking and brute-force cosine KNN run in
Lean over all rows (fine at this scale); transitive `deps`/`rdeps`/`path`
run as recursive CTEs in SQLite. -/

namespace WikiRAG
open SQLite SQLite.Blob

/-- A declaration row read from the `decls` table. -/
structure Hit where
  name : String
  short : String
  kind : String
  module : String
  line : Nat
  signature : String
  doc : String
deriving Inhabited

/-- Read a `Hit` from columns `0..6` of the current statement row (see `declCols`). -/
def readDecl (st : Stmt) : IO Hit := do
  return {
    name := ← st.columnText 0
    short := ← st.columnText 1
    kind := ← st.columnText 2
    module := ← st.columnText 3
    line := (← st.columnText 4).toNat!
    signature := ← st.columnText 5
    doc := ← st.columnText 6 }

/-- Lowercase alphanumeric tokenization. -/
def tokenize (s : String) : List String :=
  let cleaned := String.ofList (s.toLower.toList.map (fun c => if c.isAlphanum then c else ' '))
  (cleaned.splitOn " ").filter (· ≠ "")

/-- Lexical relevance of a hit to query tokens (exact short-name match dominates). -/
def scoreHit (toks : List String) (h : Hit) : Float := Id.run do
  let shortL := h.short.toLower
  let nameL := h.name.toLower
  let docL := h.doc.toLower
  let sigL := h.signature.toLower
  let mut score := 0.0
  for t in toks do
    if shortL == t then score := score + 12.0
    else if containsStr shortL t then score := score + 6.0
    else if containsStr nameL t then score := score + 3.0
    if containsStr docL t then score := score + 2.0
    if containsStr sigL t then score := score + 1.0
  return score

/-- Top-`k` declarations by lexical score against `query`. -/
def lexicalSearch (db : SQLite) (query : String) (k : Nat) : IO (Array (Float × Hit)) := do
  let s ← db.prepare s!"SELECT {declCols} FROM decls"
  let mut hits : Array Hit := #[]
  while (← s.step) do hits := hits.push (← readDecl s)
  let toks := tokenize query
  let scored := hits.filterMap (fun h =>
    let sc := scoreHit toks h
    if sc > 0.0 then some (sc, h) else none)
  let sorted := scored.qsort (fun a b => a.1 > b.1)
  return sorted.extract 0 k

/-- Top-`k` declarations by cosine similarity to a query embedding (embedded rows only). -/
def vectorSearch (db : SQLite) (qvec : Array Float) (k : Nat) : IO (Array (Float × Hit)) := do
  let s ← db.prepare s!"SELECT {declCols}, embedding FROM decls WHERE embedding IS NOT NULL"
  let mut acc : Array (Float × Hit) := #[]
  while (← s.step) do
    let h ← readDecl s
    let blob ← s.columnBlob 7
    match (fromBinary blob : Except String (Array Float)) with
    | .ok v => acc := acc.push (cosine qvec v, h)
    | .error _ => pure ()
  let sorted := acc.qsort (fun a b => a.1 > b.1)
  return sorted.extract 0 k

/-- Resolve a (possibly short) name to matching full names, shortest first. -/
def resolveName (db : SQLite) (q : String) : IO (Array String) := do
  let s ← db.prepare "SELECT DISTINCT name FROM decls WHERE name = ? OR short = ? OR name = 'DeepWiki.'||? ORDER BY length(name)"
  s.bindText 1 q
  s.bindText 2 q
  s.bindText 3 q
  let mut acc : Array String := #[]
  while (← s.step) do acc := acc.push (← s.columnText 0)
  return acc

/-- Look up a single decl by exact full name. -/
def getDecl (db : SQLite) (name : String) : IO (Option Hit) := do
  let s ← db.prepare s!"SELECT {declCols} FROM decls WHERE name = ?"
  s.bindText 1 name
  if (← s.step) then return some (← readDecl s) else return none

/-- Transitive dependencies (`reverse := false`) or dependents (`true`) up to `depth`,
returned with the shortest distance. -/
def transitive (db : SQLite) (root : String) (depth : Nat) (reverse : Bool) : IO (Array (Nat × Hit)) := do
  let joinOn := if reverse then "e.dst = d.n" else "e.src = d.n"
  let nextCol := if reverse then "e.src" else "e.dst"
  let sql := s!"WITH RECURSIVE d(n, depth) AS (VALUES(?, 0) UNION SELECT {nextCol}, d.depth+1 FROM edges e JOIN d ON {joinOn} WHERE d.depth < {depth}) SELECT x.name, x.short, x.kind, x.module, x.line, x.signature, x.doc, d.depth FROM d JOIN decls x ON x.name = d.n WHERE d.n <> ? ORDER BY d.depth, x.name"
  let s ← db.prepare sql
  s.bindText 1 root
  s.bindText 2 root
  let mut acc : Array (Nat × Hit) := #[]
  while (← s.step) do
    let h ← readDecl s
    acc := acc.push ((← s.columnText 7).toNat!, h)
  return acc

/-- A shortest `uses` path from `a` to `b` (rendered with arrows), if one exists. -/
def findPath (db : SQLite) (a b : String) (maxd : Nat := 12) : IO (Option String) := do
  let sql := s!"WITH RECURSIVE p(n, path, depth) AS (VALUES(?, ?, 0) UNION SELECT e.dst, p.path || ' → ' || e.dst, p.depth+1 FROM edges e JOIN p ON e.src = p.n WHERE p.depth < {maxd} AND instr(p.path, e.dst) = 0) SELECT path FROM p WHERE n = ? ORDER BY depth LIMIT 1"
  let s ← db.prepare sql
  s.bindText 1 a
  s.bindText 2 a
  s.bindText 3 b
  if (← s.step) then return some (← s.columnText 0) else return none

/-- Every `uses` edge `(src, dst)` in the graph. -/
def allEdges (db : SQLite) : IO (Array (String × String)) := do
  let s ← db.prepare "SELECT src, dst FROM edges"
  let mut acc : Array (String × String) := #[]
  while (← s.step) do acc := acc.push (← s.columnText 0, ← s.columnText 1)
  return acc

/-- Node `Hit`s in the depth-bounded neighborhood of `root`: forward `uses` if `fwd`,
reverse dependents if `bwd`; always includes `root`, deduplicated by name. -/
def neighborhood (db : SQLite) (root : String) (depth : Nat) (fwd bwd : Bool) : IO (Array Hit) := do
  let mut raw : Array Hit := #[]
  match (← getDecl db root) with
  | some h => raw := raw.push h
  | none => pure ()
  if fwd then for (_, h) in (← transitive db root depth false) do raw := raw.push h
  if bwd then for (_, h) in (← transitive db root depth true) do raw := raw.push h
  let mut seen : Array String := #[]
  let mut out : Array Hit := #[]
  for h in raw do
    unless seen.contains h.name do
      seen := seen.push h.name
      out := out.push h
  return out

/-- All module names (graph node set for the module graph). -/
def moduleNodes (db : SQLite) : IO (Array String) := do
  let s ← db.prepare "SELECT DISTINCT module FROM decls ORDER BY module"
  let mut acc : Array String := #[]
  while (← s.step) do acc := acc.push (← s.columnText 0)
  return acc

/-- Module dependency edges `(src, dst, weight)` (weight = number of cross-module uses). -/
def moduleGraph (db : SQLite) : IO (Array (String × String × Nat)) := do
  let s ← db.prepare "SELECT src, dst, weight FROM module_edges"
  let mut acc : Array (String × String × Nat) := #[]
  while (← s.step) do acc := acc.push (← s.columnText 0, ← s.columnText 1, (← s.columnText 2).toNat!)
  return acc

end WikiRAG
