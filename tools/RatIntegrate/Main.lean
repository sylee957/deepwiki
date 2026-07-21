import DeepWiki.CAlgebra.Frontend.Syntax
import DeepWiki.CAlgebra.Frontend.Simplify
import DeepWiki.CAlgebra.Frontend.Integrate

/-! # `integrate` — the verified rational-integration CLI

Parse a rational-function expression in `x` over `ℚ`, run the verified integration
pipeline (`ratIntegrate` — soundness `D(∫f) = f` proven end to end), and print the
antiderivative. Usage: `lake exe integrate "<expression>"`. -/

open DeepWiki.CAlgebra

def main (args : List String) : IO UInt32 := do
  match args with
  | [s] =>
    match Frontend.parseExpr s with
    | none =>
        IO.eprintln s!"integrate: cannot parse '{s}'"
        return 1
    | some e =>
        let res := (Expr.integrateAst (R := ℚ) e).simplify
        IO.println s!"∫ ({Expr.print e}) dx = {res.print} + C"
        return 0
  | _ =>
    IO.eprintln "usage: lake exe integrate \"<rational expression in x over ℚ>\""
    return 1
