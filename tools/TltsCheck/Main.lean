import TltsCheck.Db

/-! # `tlts` — CLI for the formally-verified timed model checker
The model lives in SQLite as relational rows; commands push rows (`new`/`edge`/`guard`/`reset`/
`inv`/`inv-guard` build an automaton, `formula`/`node` build a timed-HML formula). `check A F`
reconstructs both from rows and runs the verified checker — the printed Boolean is proved equal to
the semantic `A ⊨ F` by `TltsCheck.check_iff`. Evaluation is native/compiled. -/

open TltsCheck DeepWiki.ReactiveSystems

/-- Parse a required natural-number argument (errors out the CLI on bad input). -/
def reqNat (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"expected a number, got '{s}'")

/-- Parse a required comparison keyword `le|lt|eq|ge|gt`. -/
def reqCmp (s : String) : IO Cmp :=
  match cmpOfString s with
  | some c => pure c
  | none => throw (IO.userError s!"bad comparison '{s}' (use le/lt/eq/ge/gt)")

/-- `node <formula> <id> <kind> [args]` — push one formula-tree node (args depend on kind). -/
def cmdNode (db : SQLite) (formula : String) (id : Nat) (kind : String)
    (rest : List String) : IO Unit := do
  match kind, rest with
  | "tt", _ => addNode db formula id "tt" "" 0 "" 0 0 0
  | "ff", _ => addNode db formula id "ff" "" 0 "" 0 0 0
  | "and", c1 :: c2 :: _ => addNode db formula id "and" "" 0 "" 0 (← reqNat c1) (← reqNat c2)
  | "or",  c1 :: c2 :: _ => addNode db formula id "or"  "" 0 "" 0 (← reqNat c1) (← reqNat c2)
  | "dia", act :: c1 :: _ => addNode db formula id "dia" act 0 "" 0 (← reqNat c1) 0
  | "box", act :: c1 :: _ => addNode db formula id "box" act 0 "" 0 (← reqNat c1) 0
  | "ex",  c1 :: _ => addNode db formula id "ex" "" 0 "" 0 (← reqNat c1) 0
  | "fa",  c1 :: _ => addNode db formula id "fa" "" 0 "" 0 (← reqNat c1) 0
  | "reset", clk :: c1 :: _ => addNode db formula id "reset" "" (← reqNat clk) "" 0 (← reqNat c1) 0
  | "g", clk :: cmp :: c :: _ => do
      let _ ← reqCmp cmp
      addNode db formula id "g" "" (← reqNat clk) cmp (← reqNat c) 0 0
  | k, _ => throw (IO.userError s!"node kind '{k}': bad or missing arguments")
  IO.println s!"node {id} = {kind}"

def usage : String := String.intercalate "\n"
  [ "usage: tlts <command>   (model timed automata in SQLite; check is formally verified)",
    "  build an automaton:",
    "    new   <A> <nclocks> [init]      create/reset automaton A",
    "    edge  <A> <src> <act> <dst>     add an edge (prints its id #E)",
    "    guard <E> <clk> <cmp> <const>   add a guard atom to edge #E   (cmp: le|lt|eq|ge|gt)",
    "    reset <E> <clk>                 reset a clock on edge #E",
    "    inv   <A> <loc>                 add a location invariant (prints its id #I)",
    "    inv-guard <I> <clk> <cmp> <const>   add an atom to invariant #I",
    "  build a formula (a tree of nodes; root = node given to `formula`):",
    "    formula <F> <root>              create/reset formula F with root node id",
    "    node <F> <id> tt|ff",
    "    node <F> <id> and|or <c1> <c2>",
    "    node <F> <id> dia|box <act> <c1>",
    "    node <F> <id> ex|fa <c1>",
    "    node <F> <id> reset <clk> <c1>",
    "    node <F> <id> g <clk> <cmp> <const>",
    "  inspect / check:",
    "    list | formulas                 list stored automata / formulas",
    "    show <A>                        print automaton A",
    "    rm <A>                          delete automaton A",
    "    check <A> <F>                   verified: does A satisfy F?" ]

def main (args : List String) : IO Unit := do
  match args with
  | "new" :: name :: nc :: rest =>
      let db ← openDb
      let n ← reqNat nc
      let init ← match rest with | i :: _ => reqNat i | [] => pure 0
      newAuto db name n init
      IO.println s!"created '{name}': {n} clock(s), init loc {init}"
  | "edge" :: auto :: src :: act :: dst :: _ =>
      let db ← openDb
      let eid ← addEdge db auto (← reqNat src) act (← reqNat dst)
      IO.println s!"edge #{eid}: {src} --{act}--> {dst}"
  | "guard" :: eid :: clk :: cmp :: c :: _ =>
      let db ← openDb
      addEdgeGuard db (← reqNat eid) (← reqNat clk) (← reqCmp cmp) (← reqNat c)
      IO.println s!"edge #{eid} guard: clock {clk} {cmp} {c}"
  | "reset" :: eid :: clk :: _ =>
      let db ← openDb
      addEdgeReset db (← reqNat eid) (← reqNat clk)
      IO.println s!"edge #{eid} resets clock {clk}"
  | "inv" :: auto :: loc :: _ =>
      let db ← openDb
      let iid ← addInv db auto (← reqNat loc)
      IO.println s!"invariant #{iid} on '{auto}' loc {loc}"
  | "inv-guard" :: iid :: clk :: cmp :: c :: _ =>
      let db ← openDb
      addInvGuard db (← reqNat iid) (← reqNat clk) (← reqCmp cmp) (← reqNat c)
      IO.println s!"invariant #{iid} guard: clock {clk} {cmp} {c}"
  | "formula" :: name :: root :: _ =>
      let db ← openDb
      newFormula db name (← reqNat root)
      IO.println s!"created formula '{name}' (root node {root})"
  | "node" :: formula :: id :: kind :: rest =>
      let db ← openDb
      cmdNode db formula (← reqNat id) kind rest
  | ["list"] =>
      let db ← openDb
      let names ← listAutomata db
      IO.println s!"automata ({names.size}):"
      for n in names do IO.println s!"  {n}"
  | ["formulas"] =>
      let db ← openDb
      let names ← listFormulas db
      IO.println s!"formulas ({names.size}):"
      for n in names do IO.println s!"  {n}"
  | "show" :: name :: _ =>
      let db ← openDb
      match (← loadAuto db name) with
      | .error m => IO.eprintln s!"error: {m}"
      | .ok R => IO.println (reprStr R)
  | "rm" :: name :: _ =>
      let db ← openDb
      rmAuto db name
      IO.println s!"removed '{name}'"
  | "check" :: auto :: formula :: _ =>
      let db ← openDb
      match (← loadAuto db auto), (← loadFormula db formula) with
      | .error m, _ => IO.eprintln s!"error: {m}"
      | _, .error m => IO.eprintln s!"error: {m}"
      | .ok R, .ok F =>
        match buildAndCheck R F with
        | .error m => IO.eprintln s!"build error: {m}"
        | .ok b => IO.println s!"{auto} ⊨ {formula} : {b}"
  | _ => IO.println usage
