import WikiRAG.Basic
import Std.Data.HashMap

/-! # Evolutionary (co-change) coupling, mined from git into the graph

The `cochange` table records how often two modules change in the same commit — the evolutionary/
logical coupling of Gall & Zimmermann (files that change together belong together). Persisted in
`graph.db` alongside the `uses`-graph so the modularity engine reads it as the `evo` objective. -/

namespace WikiRAG
open Std SQLite

/-- `DeepWiki/SymbolicIntegration/Foo.lean` → `DeepWiki.SymbolicIntegration.Foo` (a `.lean` under `DeepWiki/`). -/
def pathToModule (p : String) : Option String :=
  let p := p.trimAscii
  if p.endsWith ".lean" && p.startsWith "DeepWiki/" then
    some ((p.dropEnd 5).replace "/" ".")
  else none

/-- Mine module co-change from `git log --name-only` and store it in the `cochange` table. -/
def mineCochange (db : SQLite) : IO Unit := do
  db.exec "DROP TABLE IF EXISTS cochange; CREATE TABLE cochange (a TEXT, b TEXT, weight INTEGER, PRIMARY KEY(a,b));"
  let out ← IO.Process.run
    { cmd := "git", args := #["log", "--no-merges", "--pretty=format:@%H", "--name-only", "--", "DeepWiki"] }
  -- group changed files into per-commit module sets
  let mut commits : Array (Array String) := #[]
  let mut cur : Array String := #[]
  for line in out.splitOn "\n" do
    if line.startsWith "@" then
      if !cur.isEmpty then commits := commits.push cur
      cur := #[]
    else
      match pathToModule line with
      | some m => if !cur.contains m then cur := cur.push m
      | none => pure ()
  if !cur.isEmpty then commits := commits.push cur
  -- count co-changing module pairs (a < b)
  let mut pairs : HashMap String Nat := {}
  for ms in commits do
    for i in [0:ms.size] do
      for j in [i+1:ms.size] do
        let a := ms[i]!; let b := ms[j]!
        let key := if a < b then s!"{a}||{b}" else s!"{b}||{a}"
        pairs := pairs.insert key ((pairs.getD key 0) + 1)
  let ins ← db.prepare "INSERT OR REPLACE INTO cochange (a,b,weight) VALUES (?,?,?)"
  for (k, w) in pairs.toArray do
    let ps := k.splitOn "||"
    ins.bindText 1 (ps.getD 0 "")
    ins.bindText 2 (ps.getD 1 "")
    ins.bindText 3 (toString w)
    ins.exec
    ins.reset
  IO.println s!"Mined co-change: {commits.size} commits → {pairs.size} co-changing module pairs."

/-- Load the `cochange` table into a `"a||b"` (a<b) → weight map; empty if not mined yet. -/
def loadCochange (db : SQLite) : IO (HashMap String Nat) := do
  let mut m : HashMap String Nat := {}
  try
    let s ← db.prepare "SELECT a, b, weight FROM cochange"
    while (← s.step) do
      m := m.insert s!"{← s.columnText 0}||{← s.columnText 1}" (← s.columnText 2).toNat!
  catch _ => pure ()
  return m

end WikiRAG
