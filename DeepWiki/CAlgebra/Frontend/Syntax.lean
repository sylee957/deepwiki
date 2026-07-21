import DeepWiki.CAlgebra.Frontend.Expr
import DeepWiki.CAlgebra.Frontend.IntegralExpr

/-! # Parser and printer for the integration frontend

A precedence-aware printer for input expressions and the antiderivative output syntax,
and a total (fueled) precedence-climbing parser for `ℚ`-expressions — rationals arise
from integer literals and `/`. Round trips are checked semantically (`toFrac` equality is
decidable), not syntactically. -/

namespace DeepWiki.CAlgebra

universe u

/-! ## Printing -/

section Print

/-- Print a dense polynomial in the variable `var`, highest degree first. -/
def DensePoly.print {S : Type u} [Zero S] [One S] [DecidableEq S] [ToString S]
    (var : String) (p : DensePoly S) : String :=
  let terms := (List.range p.size).reverse.filterMap fun k =>
    let c := p.coeff k
    if c = 0 then none
    else some <|
      if k = 0 then toString c
      else
        let xpow := if k = 1 then var else s!"{var}^{k}"
        if c = 1 then xpow else s!"{toString c}*{xpow}"
  if terms.isEmpty then "0" else String.intercalate " + " terms

/-- Polynomials print with their `z`-variable rendering (used for nested coefficients). -/
instance {S : Type u} [Zero S] [One S] [DecidableEq S] [ToString S] :
    ToString (DensePoly S) := ⟨fun p => s!"({DensePoly.print "z" p})"⟩

variable {R : Type u} [Field R] [DecidableEq R] [ToString R]

/-- Print a canonical fraction in the variable `x`. -/
def DenseFrac.print (f : DenseFrac R) : String :=
  if f.den.toPoly = 1 then DensePoly.print "x" f.num
  else s!"({DensePoly.print "x" f.num})/({DensePoly.print "x" f.den.toPoly})"

namespace Expr

/-- Precedence-aware printer: parenthesize a child rendered at lower precedence. -/
def printPrec : Expr R → ℕ → String
  | const c, _ => toString c
  | X, _ => "x"
  | add a b, prec =>
      let s := s!"{a.printPrec 65} + {b.printPrec 66}"
      if prec > 65 then s!"({s})" else s
  | sub a b, prec =>
      let s := s!"{a.printPrec 65} - {b.printPrec 66}"
      if prec > 65 then s!"({s})" else s
  | mul a b, prec =>
      let s := s!"{a.printPrec 70} * {b.printPrec 71}"
      if prec > 70 then s!"({s})" else s
  | div a b, prec =>
      let s := s!"{a.printPrec 70} / {b.printPrec 71}"
      if prec > 70 then s!"({s})" else s
  | neg a, prec =>
      let s := s!"-{a.printPrec 75}"
      if prec > 75 then s!"({s})" else s
  | inv a, _ => s!"{a.printPrec 81}⁻¹"
  | pow a n, prec =>
      let s := s!"{a.printPrec 81}^{n}"
      if prec > 80 then s!"({s})" else s

/-- Print an expression. -/
def print (e : Expr R) : String := e.printPrec 0

end Expr

/-- Print an antiderivative expression: fractions, `RootSum` log classes, sums. -/
def IntegralExpr.print : IntegralExpr R → String
  | .frac f => DenseFrac.print f
  | .rootSum Q S =>
      s!"RootSum({DensePoly.print "z" Q}, α ↦ α·log({DensePoly.print "x" S}[z := α]))"
  | .smulLog a u => s!"{toString a}·log({DensePoly.print "x" u})"
  | .add a b => s!"{a.print} + {b.print}"

end Print

/-! ## Parsing (over `ℚ`) -/

namespace Frontend

/-- Tokens of the expression grammar. -/
inductive Tok where
  /-- A natural-number literal. -/
  | num (n : ℕ)
  /-- The variable `x`. -/
  | x
  /-- `+`. -/
  | plus
  /-- `-`. -/
  | minus
  /-- `*`. -/
  | star
  /-- `/`. -/
  | slash
  /-- `^`. -/
  | caret
  /-- `(`. -/
  | lp
  /-- `)`. -/
  | rp
  deriving DecidableEq, Repr

/-- Take a maximal digit run. -/
def takeDigits : List Char → ℕ → ℕ × List Char
  | c :: cs, acc =>
      if c.isDigit then takeDigits cs (10 * acc + (c.toNat - '0'.toNat))
      else (acc, c :: cs)
  | [], acc => (acc, [])

/-- Tokenize a character list (fueled by its length). -/
def tokenizeAux : ℕ → List Char → Option (List Tok)
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => some []
  | fuel + 1, c :: cs =>
      if c = ' ' then tokenizeAux fuel cs
      else if c = 'x' then (tokenizeAux fuel cs).map (Tok.x :: ·)
      else if c = '+' then (tokenizeAux fuel cs).map (Tok.plus :: ·)
      else if c = '-' then (tokenizeAux fuel cs).map (Tok.minus :: ·)
      else if c = '*' then (tokenizeAux fuel cs).map (Tok.star :: ·)
      else if c = '/' then (tokenizeAux fuel cs).map (Tok.slash :: ·)
      else if c = '^' then (tokenizeAux fuel cs).map (Tok.caret :: ·)
      else if c = '(' then (tokenizeAux fuel cs).map (Tok.lp :: ·)
      else if c = ')' then (tokenizeAux fuel cs).map (Tok.rp :: ·)
      else if c.isDigit then
        let (n, rest) := takeDigits (c :: cs) 0
        (tokenizeAux fuel rest).map (Tok.num n :: ·)
      else none

/-- Tokenize a string. -/
def tokenize (s : String) : Option (List Tok) :=
  tokenizeAux s.length s.toList

mutual

/-- Parse a primary expression, then climb binary operators of precedence `≥ prec`. -/
def parseP : ℕ → ℕ → List Tok → Option (Expr ℚ × List Tok)
  | 0, _, _ => none
  | fuel + 1, prec, ts =>
      (match ts with
        | .num n :: rest => some (Expr.const (n : ℚ), rest)
        | .x :: rest => some (Expr.X, rest)
        | .minus :: rest =>
            (parseP fuel 75 rest).map fun (e, r) => (Expr.neg e, r)
        | .lp :: rest =>
            match parseP fuel 0 rest with
            | some (e, .rp :: r) => some (e, r)
            | _ => none
        | _ => none).bind fun (lhs, rest) => climb fuel prec lhs rest

/-- Left-associative operator climbing. -/
def climb : ℕ → ℕ → Expr ℚ → List Tok → Option (Expr ℚ × List Tok)
  | 0, _, _, _ => none
  | fuel + 1, prec, lhs, ts =>
      match ts with
      | .plus :: rest =>
          if 65 ≥ prec then
            (parseP fuel 66 rest).bind fun (rhs, r) => climb fuel prec (.add lhs rhs) r
          else some (lhs, ts)
      | .minus :: rest =>
          if 65 ≥ prec then
            (parseP fuel 66 rest).bind fun (rhs, r) => climb fuel prec (.sub lhs rhs) r
          else some (lhs, ts)
      | .star :: rest =>
          if 70 ≥ prec then
            (parseP fuel 71 rest).bind fun (rhs, r) => climb fuel prec (.mul lhs rhs) r
          else some (lhs, ts)
      | .slash :: rest =>
          if 70 ≥ prec then
            (parseP fuel 71 rest).bind fun (rhs, r) => climb fuel prec (.div lhs rhs) r
          else some (lhs, ts)
      | .caret :: .num n :: rest =>
          if 80 ≥ prec then climb fuel prec (.pow lhs n) rest
          else some (lhs, ts)
      | _ => some (lhs, ts)

end

/-- Parse a `ℚ`-expression from a string (total; `none` on malformed input). -/
def parseExpr (s : String) : Option (Expr ℚ) := do
  let ts ← tokenize s
  match parseP (2 * ts.length + 2) 0 ts with
  | some (e, []) => some e
  | _ => none

end Frontend


end DeepWiki.CAlgebra
