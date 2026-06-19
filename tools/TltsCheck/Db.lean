import SQLite
import TltsCheck.Build

/-! # Relational SQLite store for `tlts` — no parsing, only rows
The model is *relationalized*: an automaton is `automata` + `edges` + `edge_guard` (atoms) +
`edge_reset` rows + `invariants`/`inv_guard` rows; a formula is `formula_node` rows (a tree by id).
The CLI pushes rows; `loadAuto`/`loadFormula` read rows back into `RawAuto`/`RawMt` by reconstruction
(the `cmp` column is enum-decoded with `cmpOfString`, a lookup — not grammar-parsing). Path:
`$TLTS_DB`, default `.tlts/models.db`. -/

namespace TltsCheck

open SQLite DeepWiki.ReactiveSystems

def dbPath : IO String := do pure ((← IO.getEnv "TLTS_DB").getD ".tlts/models.db")

/-- Open (creating if needed) the model database and ensure the relational schema. -/
def openDb : IO SQLite := do
  let p ← dbPath
  if let some dir := (System.FilePath.mk p).parent then IO.FS.createDirAll dir
  let db ← SQLite.«open» p
  for ddl in
    [ "CREATE TABLE IF NOT EXISTS automata (name TEXT PRIMARY KEY, num_clocks INTEGER, init INTEGER);",
      "CREATE TABLE IF NOT EXISTS edges (id INTEGER PRIMARY KEY AUTOINCREMENT, auto TEXT, src INTEGER, act TEXT, dst INTEGER);",
      "CREATE TABLE IF NOT EXISTS edge_guard (edge_id INTEGER, clock INTEGER, cmp TEXT, k INTEGER);",
      "CREATE TABLE IF NOT EXISTS edge_reset (edge_id INTEGER, clock INTEGER);",
      "CREATE TABLE IF NOT EXISTS invariants (id INTEGER PRIMARY KEY AUTOINCREMENT, auto TEXT, loc INTEGER);",
      "CREATE TABLE IF NOT EXISTS inv_guard (inv_id INTEGER, clock INTEGER, cmp TEXT, k INTEGER);",
      "CREATE TABLE IF NOT EXISTS formulas (name TEXT PRIMARY KEY, root INTEGER);",
      "CREATE TABLE IF NOT EXISTS formula_node (formula TEXT, id INTEGER, kind TEXT, act TEXT, clock INTEGER, cmp TEXT, k INTEGER, c1 INTEGER, c2 INTEGER);" ] do
    db.exec ddl
  pure db

/-- The rowid of the most recent INSERT. -/
def lastRowId (db : SQLite) : IO Nat := do
  let s ← db.prepare "SELECT last_insert_rowid()"
  let _ ← s.step
  pure (← s.columnText 0).toNat!

/-- One prepared-and-bound text-only insert (binds `args` to `?` positionally, executes). -/
private def insert (db : SQLite) (sql : String) (args : List String) : IO Unit := do
  let s ← db.prepare sql
  let mut i := 1
  for a in args do s.bindText i a; i := i + 1
  s.exec

/-! ## Model-building inserts (one row per CLI command) -/

/-- Delete an automaton's edges (with their guards/resets) and invariants (with their guards). -/
private def clearAuto (db : SQLite) (name : String) : IO Unit := do
  let e ← db.prepare "SELECT id FROM edges WHERE auto = ?"
  e.bindText 1 name
  while (← e.step) do
    let eid := (← e.columnText 0)
    insert db "DELETE FROM edge_guard WHERE edge_id = ?" [eid]
    insert db "DELETE FROM edge_reset WHERE edge_id = ?" [eid]
  let i ← db.prepare "SELECT id FROM invariants WHERE auto = ?"
  i.bindText 1 name
  while (← i.step) do insert db "DELETE FROM inv_guard WHERE inv_id = ?" [(← i.columnText 0)]
  insert db "DELETE FROM edges WHERE auto = ?" [name]
  insert db "DELETE FROM invariants WHERE auto = ?" [name]

/-- Create (or reset) an automaton, clearing its edges/invariants. -/
def newAuto (db : SQLite) (name : String) (nclocks init : Nat) : IO Unit := do
  clearAuto db name
  insert db "INSERT OR REPLACE INTO automata (name, num_clocks, init) VALUES (?, ?, ?)"
    [name, toString nclocks, toString init]

/-- Delete an automaton and all its rows. -/
def rmAuto (db : SQLite) (name : String) : IO Unit := do
  clearAuto db name
  insert db "DELETE FROM automata WHERE name = ?" [name]

/-- Add an edge `src --act--> dst`; returns the new edge id. -/
def addEdge (db : SQLite) (auto : String) (src : Nat) (act : String) (dst : Nat) : IO Nat := do
  insert db "INSERT INTO edges (auto, src, act, dst) VALUES (?, ?, ?, ?)"
    [auto, toString src, act, toString dst]
  lastRowId db

/-- Add a guard atom `clock cmp k` to an edge. -/
def addEdgeGuard (db : SQLite) (eid clock : Nat) (cmp : Cmp) (k : Nat) : IO Unit :=
  insert db "INSERT INTO edge_guard (edge_id, clock, cmp, k) VALUES (?, ?, ?, ?)"
    [toString eid, toString clock, cmpToKey cmp, toString k]

/-- Add a reset clock to an edge. -/
def addEdgeReset (db : SQLite) (eid clock : Nat) : IO Unit :=
  insert db "INSERT INTO edge_reset (edge_id, clock) VALUES (?, ?)" [toString eid, toString clock]

/-- Add a location invariant; returns its id (atoms attached via `addInvGuard`). -/
def addInv (db : SQLite) (auto : String) (loc : Nat) : IO Nat := do
  insert db "INSERT INTO invariants (auto, loc) VALUES (?, ?)" [auto, toString loc]
  lastRowId db

/-- Add a guard atom to an invariant. -/
def addInvGuard (db : SQLite) (iid clock : Nat) (cmp : Cmp) (k : Nat) : IO Unit :=
  insert db "INSERT INTO inv_guard (inv_id, clock, cmp, k) VALUES (?, ?, ?, ?)"
    [toString iid, toString clock, cmpToKey cmp, toString k]

/-- Create (or reset) a formula with the given root node id. -/
def newFormula (db : SQLite) (name : String) (root : Nat) : IO Unit := do
  insert db "DELETE FROM formula_node WHERE formula = ?" [name]
  insert db "INSERT OR REPLACE INTO formulas (name, root) VALUES (?, ?)" [name, toString root]

/-- Add a formula node `(id, kind, act, clock, cmp, k, c1, c2)` (unused fields ignored). -/
def addNode (db : SQLite) (formula : String) (id : Nat) (kind act : String)
    (clock : Nat) (cmp : String) (k c1 c2 : Nat) : IO Unit :=
  insert db "INSERT INTO formula_node (formula, id, kind, act, clock, cmp, k, c1, c2) VALUES (?,?,?,?,?,?,?,?,?)"
    [formula, toString id, kind, act, toString clock, cmp, toString k, toString c1, toString c2]

/-! ## Loaders (rows → typed-builder input; no parsing) -/

/-- Names of all stored automata. -/
def listAutomata (db : SQLite) : IO (Array String) := do
  let s ← db.prepare "SELECT name FROM automata ORDER BY name"
  let mut acc := #[]
  while (← s.step) do acc := acc.push (← s.columnText 0)
  pure acc

/-- Names of all stored formulas. -/
def listFormulas (db : SQLite) : IO (Array String) := do
  let s ← db.prepare "SELECT name FROM formulas ORDER BY name"
  let mut acc := #[]
  while (← s.step) do acc := acc.push (← s.columnText 0)
  pure acc

/-- Read a guard's atoms (from `edge_guard`/`inv_guard`) into a `RawCC` (conjunction). -/
private def loadGuard (db : SQLite) (table idCol : String) (id : Nat) : IO (Except String RawCC) := do
  let s ← db.prepare s!"SELECT clock, cmp, k FROM {table} WHERE {idCol} = ?"
  s.bindText 1 (toString id)
  let mut acc : RawCC := .true_
  while (← s.step) do
    let clk := (← s.columnText 0).toNat!
    let kk := (← s.columnText 2).toNat!
    match cmpOfString (← s.columnText 1) with
    | none => return .error s!"bad comparison in {table}"
    | some c => acc := (match acc with | .true_ => .atom clk c kk | r => .and (.atom clk c kk) r)
  return .ok acc

/-- Reconstruct a `RawAuto` from its rows. -/
def loadAuto (db : SQLite) (name : String) : IO (Except String RawAuto) := do
  let a ← db.prepare "SELECT num_clocks, init FROM automata WHERE name = ?"
  a.bindText 1 name
  if !(← a.step) then return .error s!"no automaton '{name}' (try `tlts list`)"
  let numClocks := (← a.columnText 0).toNat!
  let init := (← a.columnText 1).toNat!
  let mut edges : List (Nat × String × Nat × RawCC × List Nat) := []
  let es ← db.prepare "SELECT id, src, act, dst FROM edges WHERE auto = ? ORDER BY id"
  es.bindText 1 name
  let mut rows : List (Nat × Nat × String × Nat) := []
  while (← es.step) do
    rows := rows ++ [((← es.columnText 0).toNat!, (← es.columnText 1).toNat!,
                      (← es.columnText 2), (← es.columnText 3).toNat!)]
  for (eid, src, act, dst) in rows do
    let g ← loadGuard db "edge_guard" "edge_id" eid
    match g with
    | .error m => return .error m
    | .ok g =>
      let rs ← db.prepare "SELECT clock FROM edge_reset WHERE edge_id = ?"
      rs.bindText 1 (toString eid)
      let mut resets : List Nat := []
      while (← rs.step) do resets := resets ++ [(← rs.columnText 0).toNat!]
      edges := edges ++ [(src, act, dst, g, resets)]
  let mut invs : List (Nat × RawCC) := []
  let is ← db.prepare "SELECT id, loc FROM invariants WHERE auto = ?"
  is.bindText 1 name
  let mut irows : List (Nat × Nat) := []
  while (← is.step) do irows := irows ++ [((← is.columnText 0).toNat!, (← is.columnText 1).toNat!)]
  for (iid, loc) in irows do
    match (← loadGuard db "inv_guard" "inv_id" iid) with
    | .error m => return .error m
    | .ok g => invs := invs ++ [(loc, g)]
  return .ok { numClocks := numClocks, init := init, edges := edges, invs := invs }

/-- A `formula_node` row. -/
private structure NodeRow where
  id : Nat
  kind : String
  act : String
  clock : Nat
  cmp : String
  k : Nat
  c1 : Nat
  c2 : Nat

/-- Reconstruct a `RawMt` tree from its node rows, starting at `root`. -/
partial def buildNode (nodes : List NodeRow) (id : Nat) : Except String RawMt :=
  match nodes.find? (·.id == id) with
  | none => throw s!"formula node {id} missing"
  | some n => match n.kind with
    | "tt" => pure .tt
    | "ff" => pure .ff
    | "and" => return .and (← buildNode nodes n.c1) (← buildNode nodes n.c2)
    | "or"  => return .or  (← buildNode nodes n.c1) (← buildNode nodes n.c2)
    | "dia" => return .dia n.act (← buildNode nodes n.c1)
    | "box" => return .box n.act (← buildNode nodes n.c1)
    | "ex"  => return .ex (← buildNode nodes n.c1)
    | "fa"  => return .fa (← buildNode nodes n.c1)
    | "reset" => return .reset n.clock (← buildNode nodes n.c1)
    | "g" => match cmpOfString n.cmp with
        | some c => pure (.guard (.atom n.clock c n.k))
        | none => throw s!"bad comparison '{n.cmp}' in formula node {id}"
    | k => throw s!"unknown formula node kind '{k}'"

/-- Reconstruct a `RawMt` from its rows. -/
def loadFormula (db : SQLite) (name : String) : IO (Except String RawMt) := do
  let f ← db.prepare "SELECT root FROM formulas WHERE name = ?"
  f.bindText 1 name
  if !(← f.step) then return .error s!"no formula '{name}' (try `tlts formulas`)"
  let root := (← f.columnText 0).toNat!
  let ns ← db.prepare "SELECT id, kind, act, clock, cmp, k, c1, c2 FROM formula_node WHERE formula = ?"
  ns.bindText 1 name
  let mut nodes : List NodeRow := []
  while (← ns.step) do
    let id := (← ns.columnText 0).toNat!
    let kind := (← ns.columnText 1)
    let act := (← ns.columnText 2)
    let clock := (← ns.columnText 3).toNat!
    let cmp := (← ns.columnText 4)
    let k := (← ns.columnText 5).toNat!
    let c1 := (← ns.columnText 6).toNat!
    let c2 := (← ns.columnText 7).toNat!
    nodes := nodes ++ [(⟨id, kind, act, clock, cmp, k, c1, c2⟩ : NodeRow)]
  return buildNode nodes root

end TltsCheck
