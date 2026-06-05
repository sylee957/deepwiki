/-
verso-parse: a standalone executable that parses a Book/*.lean Verso document
using Verso's own markup parser and emits a JSON block+inline tree for the
VSCode preview extension. Parse-only (empty environment, no elaboration), so it
runs in ~25ms on real chapters.

The preview consumes this JSON instead of re-implementing the Verso grammar in
TypeScript: the single source of markup truth is Verso's parser.
-/
import Verso.Parser
import Verso.SyntaxUtils
import Lean.Data.Json
open Verso.Parser
open Lean Lean.Parser

namespace VersoParse

/-- Small helpers over `Lean.Json` so the walkers read cleanly. -/
abbrev J := Json
def jnat (n : Nat) : J := Json.num (JsonNumber.fromNat n)

/-- A node's source range as {sl,sc,el,ec} (1-based line, 0-based col). -/
def rangeJ (fm : FileMap) (stx : Syntax) : J :=
  match stx.getPos?, stx.getTailPos? with
  | some p, some t =>
    let a := fm.toPosition p
    let b := fm.toPosition t
    Json.mkObj [("sl", jnat a.line), ("sc", jnat a.column),
                ("el", jnat b.line), ("ec", jnat b.column)]
  | some p, none =>
    let a := fm.toPosition p
    Json.mkObj [("sl", jnat a.line), ("sc", jnat a.column),
                ("el", jnat a.line), ("ec", jnat a.column)]
  | _, _ => Json.null

/-- Extract the literal string carried by a `str` node. -/
partial def strContent : Syntax → String
  | .node _ _ args => args.foldl (fun acc a => acc ++ strContent a) ""
  | .atom _ v =>
    if v.length ≥ 2 && v.front == '"' then
      (Syntax.decodeStrLit v).getD ((v.drop 1 |>.dropEnd 1).toString)
    else v
  | _ => ""

/-- The literal text of the first `str` descendant in `args`. -/
partial def childStr (args : Array Syntax) : String :=
  Id.run do
    for a in args do
      match a with
      | .node _ `str _ => return strContent a
      | .node _ _ inner =>
        let s := childStr inner
        if s != "" then return s
      | _ => pure ()
    return ""

mutual

/-- Serialize an inline node to JSON. -/
partial def inlineJ (fm : FileMap) (stx : Syntax) : Option J :=
  match stx with
  | .node _ ``Lean.Doc.Syntax.text args =>
    some (Json.mkObj [("t", Json.str "text"), ("s", Json.str (childStr args))])
  | .node _ ``Lean.Doc.Syntax.linebreak _ =>
    some (Json.mkObj [("t", Json.str "break")])
  | .node _ ``Lean.Doc.Syntax.emph args =>
    some (Json.mkObj [("t", Json.str "emph"), ("kids", inlinesJ fm args)])
  | .node _ ``Lean.Doc.Syntax.bold args =>
    some (Json.mkObj [("t", Json.str "bold"), ("kids", inlinesJ fm args)])
  | .node _ ``Lean.Doc.Syntax.code args =>
    some (Json.mkObj [("t", Json.str "code"), ("s", Json.str (childStr args))])
  | .node _ ``Lean.Doc.Syntax.inline_math args =>
    some (Json.mkObj [("t", Json.str "math"), ("display", Json.bool false),
                      ("s", Json.str (childStr args))])
  | .node _ ``Lean.Doc.Syntax.display_math args =>
    some (Json.mkObj [("t", Json.str "math"), ("display", Json.bool true),
                      ("s", Json.str (childStr args))])
  | .node _ ``Lean.Doc.Syntax.link args =>
    some (Json.mkObj [("t", Json.str "link"), ("kids", inlinesJ fm args)])
  | _ => none

/-- Collect inline children (skipping atoms / null wrappers) to a JSON array. -/
partial def inlinesJ (fm : FileMap) (args : Array Syntax) : J :=
  Id.run do
    let mut out : Array J := #[]
    for a in args do
      match a with
      | .node _ k inner =>
        if k == nullKind then
          match inlinesJ fm inner with
          | .arr xs => out := out ++ xs
          | _ => pure ()
        else if let some j := inlineJ fm a then
          out := out.push j
      | _ => pure ()
    return Json.arr out

end

/-- Header level. The parser stores `(#count − 1)` as a `num` atom (see Verso's
`header` rule), so the heading level is that value + 1: `#` → 1, `##` → 2, … -/
partial def headerLevel (args : Array Syntax) : Nat :=
  Id.run do
    for a in args do
      match a with
      | .node _ `num #[.atom _ v] => return (v.toNat?.getD 0) + 1
      | _ => pure ()
    return 1

mutual

/-- Serialize a block node to JSON, or none if unrecognized. -/
partial def blockJ (fm : FileMap) (stx : Syntax) : Option J :=
  match stx with
  | .node _ ``Lean.Doc.Syntax.para args =>
    some (Json.mkObj [("kind", Json.str "para"), ("range", rangeJ fm stx),
                      ("kids", inlinesJ fm args)])
  | .node _ ``Lean.Doc.Syntax.header args =>
    some (Json.mkObj [("kind", Json.str "header"), ("range", rangeJ fm stx),
                      ("level", jnat (headerLevel args)),
                      ("kids", inlinesJ fm args)])
  | .node _ ``Lean.Doc.Syntax.codeblock args =>
    some (Json.mkObj [("kind", Json.str "code"), ("range", rangeJ fm stx),
                      ("text", Json.str (childStr args))])
  | .node _ ``Lean.Doc.Syntax.blockquote args =>
    some (Json.mkObj [("kind", Json.str "blockquote"), ("range", rangeJ fm stx),
                      ("kids", Json.arr (blocksJ fm args))])
  | .node _ ``Lean.Doc.Syntax.ul args =>
    some (Json.mkObj [("kind", Json.str "list"), ("range", rangeJ fm stx),
                      ("ordered", Json.bool false),
                      ("items", Json.arr (listItemsJ fm args))])
  | .node _ ``Lean.Doc.Syntax.ol args =>
    some (Json.mkObj [("kind", Json.str "list"), ("range", rangeJ fm stx),
                      ("ordered", Json.bool true),
                      ("items", Json.arr (listItemsJ fm args))])
  | _ => none

/-- Each `li` becomes an array of its block children. Non-`li` args (the list's
own bullet/number markers) are skipped; `nullKind` wrappers are descended. -/
partial def listItemsJ (fm : FileMap) (args : Array Syntax) : Array J :=
  Id.run do
    let mut out : Array J := #[]
    for a in args do
      match a with
      | .node _ ``Lean.Doc.Syntax.li inner =>
        out := out.push (Json.arr (blocksJ fm inner))
      | .node _ k inner =>
        if k == nullKind then out := out ++ listItemsJ fm inner
      | _ => pure ()
    return out

/-- Walk a list of block syntaxes (descending through null wrappers). -/
partial def blocksJ (fm : FileMap) (args : Array Syntax) : Array J :=
  Id.run do
    let mut out : Array J := #[]
    for a in args do
      match a with
      | .node _ k inner =>
        if k == nullKind then
          out := out ++ blocksJ fm inner
        else if let some j := blockJ fm a then
          out := out.push j
      | _ => pure ()
    return out

end

end VersoParse

/-- Replace the Lean module header (every line up to and including the
`#doc (…) "…" =>` line) with blank lines. Blanking rather than dropping keeps
every later line at its original line number, so positions in the emitted tree
match the real file — which the preview needs for LSP queries. -/
def stripPreamble (raw : String) : String := Id.run do
  let lines := (raw.splitOn "\n").toArray
  let mut docIdx : Option Nat := none
  for i in [0:lines.size] do
    -- Trim both ends so CRLF (`\r`) and trailing spaces after `=>` don't defeat
    -- the match (`splitOn "\n"` leaves a trailing `\r` on CRLF files).
    let l := (lines[i]!).trimAscii.toString
    if l.startsWith "#doc" && l.endsWith "=>" then
      docIdx := some i
      break
  match docIdx with
  | none => return raw
  | some idx =>
    let blanked := lines.mapIdx (fun i l => if i ≤ idx then "" else l)
    return String.intercalate "\n" blanked.toList

open VersoParse in
def main (args : List String) : IO UInt32 := do
  match args with
  | [] => IO.eprintln "usage: verso-parse <file.lean>"; return 1
  | path :: _ =>
    let raw ← IO.FS.readFile path
    let input := stripPreamble raw
    let ictx := mkInputContext input path
    let env ← mkEmptyEnvironment
    let pmctx : ParserModuleContext := { env := env, options := {} }
    let s' := (document {}).run ictx pmctx (getTokenTable env)
                (mkParserState input)
    let top := s'.stxStack.extract 0 s'.stxStack.size
    let blocks := blocksJ ictx.fileMap top
    let out : J := Json.mkObj [
      ("blocks", Json.arr blocks),
      ("errors", jnat s'.allErrors.size)]
    IO.println out.compress
    return 0
