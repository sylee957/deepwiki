# `tlts` — a formally-verified timed model checker, as a CLI

`tlts` models **timed automata** as relational rows in a SQLite database and checks
**timed-HML** properties against them. The check is *formally verified*: the Boolean it
prints is proved equal to the semantic satisfaction relation `A ⊨ F` by the Lean theorem
`TltsCheck.check_iff` (`= DeepWiki.ReactiveSystems.satisfiesMt_iff_decideFull_delaySucc`),
which routes through the Alur–Dill region-successor decision procedure. Evaluation is
native/compiled, not kernel `decide`.

Like the `wiki` graph-RAG tool, this lives under `tools/` and is **out of
`defaultTargets`**, so it never touches the warning-/sorry-free math gate.

```
lake build tlts          # build
lake exe tlts            # usage
```

## Design: the database *is* the model

There is no model file format and no parser. The model is **relationalized** — every piece
is a row, and the CLI commands push rows one at a time. `check` reconstructs the
dependently-typed `FinAutomaton`/`Mt` directly from the rows (the `cmp` column is decoded by
an enum lookup, not grammar-parsing) and validates clock/location indices into `Fin n`.

Tables: `automata(name, num_clocks, init)`, `edges(id, auto, src, act, dst)`,
`edge_guard(edge_id, clock, cmp, k)` (guard = conjunction of atom rows), `edge_reset`,
`invariants(id, auto, loc)`, `inv_guard`, plus `formulas(name, root)` and
`formula_node(formula, id, kind, …, c1, c2)` (a formula is a tree of node rows, joined by id).

Database path: `$TLTS_DB`, default `.tlts/models.db` (gitignored).

## Commands

Build an automaton:

| command | effect |
|---|---|
| `tlts new <A> <nclocks> [init]` | create/reset automaton `A` |
| `tlts edge <A> <src> <act> <dst>` | add an edge — **prints its id `#E`** |
| `tlts guard <E> <clk> <cmp> <const>` | add a guard atom to edge `#E` (`cmp`: `le\|lt\|eq\|ge\|gt`) |
| `tlts reset <E> <clk>` | reset a clock on edge `#E` |
| `tlts inv <A> <loc>` | add a location invariant — prints its id `#I` |
| `tlts inv-guard <I> <clk> <cmp> <const>` | add an atom to invariant `#I` |

Build a timed-HML formula (a tree of nodes; the root is the node id passed to `formula`):

| command | node |
|---|---|
| `tlts formula <F> <root>` | create/reset formula `F` |
| `tlts node <F> <id> tt\|ff` | constant |
| `tlts node <F> <id> and\|or <c1> <c2>` | binary |
| `tlts node <F> <id> dia\|box <act> <c1>` | `⟨act⟩` / `[act]` |
| `tlts node <F> <id> ex\|fa <c1>` | `∃∃` / `∀∀` (delay) |
| `tlts node <F> <id> reset <clk> <c1>` | freeze-reset a formula clock |
| `tlts node <F> <id> g <clk> <cmp> <const>` | clock guard |

Inspect / check:

| command | effect |
|---|---|
| `tlts list` / `tlts formulas` | list stored automata / formulas |
| `tlts show <A>` | print automaton `A` |
| `tlts rm <A>` | delete automaton `A` |
| `tlts check <A> <F>` | **verified**: does `A` satisfy `F`? |

## Example

A one-clock automaton with a self-loop `a` guarded `x ≤ 1` that resets `x`, under the
invariant `x ≤ 2`. We check `∃∃[a]ff` ("after some delay, `a` is disabled" — true, once
`x > 1`) and `∀∀⟨a⟩tt` ("`a` stays enabled after every delay" — false).

```sh
tlts new A 1
tlts edge A 0 a 0       # -> edge #1
tlts guard 1 0 le 1     # x <= 1
tlts reset 1 0          # reset x
tlts inv A 0            # -> invariant #1
tlts inv-guard 1 0 le 2 # x <= 2

tlts formula P 0        # P = ∃∃[a]ff
tlts node P 0 ex 1
tlts node P 1 box a 2
tlts node P 2 ff
tlts check A P          # A ⊨ P : true

tlts formula Q 0        # Q = ∀∀⟨a⟩tt
tlts node Q 0 fa 1
tlts node Q 1 dia a 2
tlts node Q 2 tt
tlts check A Q          # A ⊨ Q : false
```
