import DeepWiki.Refine.CCOmega.Typing

/-! # Named surface syntax for CCω

Readable named terms and contexts elaborate to the intrinsically scoped de Bruijn representation
used by the checked calculus core. -/

namespace DeepWiki.Refine.CCOmega.SurfaceSyntax

open DeepWiki.Refine.DependentCalculus
open Lean Macro

/-! The object-language grammar is
`A, B, t, u ::= □[i] | x | t u | λ x : A, t | Π x : A, B`, with contexts
`Γ ::= ⟨⟩ | Γ, x : A`. -/

declare_syntax_cat ccwterm
syntax:max ident : ccwterm
syntax:max "□[" num "]" : ccwterm
syntax:max "(" ccwterm ")" : ccwterm
syntax:70 ccwterm:70 ccwterm:71 : ccwterm
syntax:25 ccwterm:26 " → " ccwterm:25 : ccwterm
syntax:20 "λ " ident " : " ccwterm ", " ccwterm : ccwterm
syntax:20 "Π " ident " : " ccwterm ", " ccwterm : ccwterm

declare_syntax_cat ccwctx
syntax:max "⟨⟩" : ccwctx
syntax:20 ccwctx ", " ident " : " ccwterm : ccwctx

/-- Find the de Bruijn index of the nearest binder carrying a surface name. -/
def nameIndex? (name : Name) : List Name → Option Nat
  | [] => none
  | current :: rest =>
      if name == current then some 0 else (nameIndex? name rest).map Nat.succ

/-- Elaborate a named surface term into an intrinsically scoped `CCω` term. -/
partial def expandTerm (scope : List Name) (stx : Syntax) :
    MacroM (TSyntax `term) := do
  match stx with
  | `(ccwterm| □[$level:num]) =>
      `(.sort $level)
  | `(ccwterm| $name:ident) =>
      let some index := nameIndex? name.getId scope
        | Macro.throwErrorAt name s!"unbound CCω variable '{name.getId}'"
      let indexSyntax := quote index
      let sizeSyntax := quote scope.length
      `(.var (⟨$indexSyntax, by decide⟩ : Fin $sizeSyntax))
  | `(ccwterm| ($term:ccwterm)) =>
      expandTerm scope term
  | `(ccwterm| $function:ccwterm $argument:ccwterm) =>
      let functionSyntax ← expandTerm scope function
      let argumentSyntax ← expandTerm scope argument
      `(.app $functionSyntax $argumentSyntax)
  | `(ccwterm| $domain:ccwterm → $codomain:ccwterm) =>
      let domainSyntax ← expandTerm scope domain
      let codomainSyntax ← expandTerm (Name.anonymous :: scope) codomain
      `(.pi $domainSyntax $codomainSyntax)
  | `(ccwterm| λ $name:ident : $domain:ccwterm, $body:ccwterm) =>
      let domainSyntax ← expandTerm scope domain
      let bodySyntax ← expandTerm (name.getId :: scope) body
      `(.lam $domainSyntax $bodySyntax)
  | `(ccwterm| Π $name:ident : $domain:ccwterm, $codomain:ccwterm) =>
      let domainSyntax ← expandTerm scope domain
      let codomainSyntax ← expandTerm (name.getId :: scope) codomain
      `(.pi $domainSyntax $codomainSyntax)
  | _ => Macro.throwErrorAt stx "unsupported CCω term syntax"

/-- Elaborate a named dependent context and return its newest-first name scope. -/
partial def expandContext (stx : Syntax) :
    MacroM (List Name × TSyntax `term) := do
  match stx with
  | `(ccwctx| ⟨⟩) =>
      let emptySyntax ← `(.empty)
      pure ([], emptySyntax)
  | `(ccwctx| $context:ccwctx, $name:ident : $type:ccwterm) =>
      let (scope, contextSyntax) ← expandContext context
      if (nameIndex? name.getId scope).isSome then
        Macro.throwErrorAt name s!"duplicate CCω context variable '{name.getId}'"
      let typeSyntax ← expandTerm scope type
      let extendedSyntax ← `(.extend $contextSyntax $typeSyntax)
      pure (name.getId :: scope, extendedSyntax)
  | _ => Macro.throwErrorAt stx "unsupported CCω context syntax"

/-- Elaborate a closed named surface term to `Term 0`. -/
syntax:max "ccω!{" ccwterm "}" : term
macro_rules
  | `(ccω!{ $term:ccwterm }) => do
      return (← expandTerm [] term).raw

/-- Elaborate a named surface context to an indexed `Context`. -/
syntax:max "ccωctx!{" ccwctx "}" : term
macro_rules
  | `(ccωctx!{ $context:ccwctx }) => do
      let (_, contextSyntax) ← expandContext context
      pure contextSyntax.raw

/-- Elaborate an open named term relative to the displayed context. -/
syntax:max "ccωterm!{" ccwctx " ⊢ " ccwterm "}" : term
macro_rules
  | `(ccωterm!{ $context:ccwctx ⊢ $term:ccwterm }) => do
      let (scope, _) ← expandContext context
      return (← expandTerm scope term).raw

/-- Elaborate a surface typing judgment directly to `HasType Γ t A`. -/
syntax:20 "ccω!{" ccwctx " ⊢ " ccwterm " : " ccwterm "}" : term
macro_rules
  | `(ccω!{ $context:ccwctx ⊢ $term:ccwterm : $type:ccwterm }) => do
      let (scope, contextSyntax) ← expandContext context
      let termSyntax ← expandTerm scope term
      let typeSyntax ← expandTerm scope type
      `(HasType $contextSyntax $termSyntax $typeSyntax)

/-- Elaborate surface definitional equality to the core beta-convertibility relation. -/
syntax:20 "ccω!{" ccwctx " ⊢ " ccwterm " ≡ " ccwterm "}" : term
macro_rules
  | `(ccω!{ $context:ccwctx ⊢ $left:ccwterm ≡ $right:ccwterm }) => do
      let (scope, _) ← expandContext context
      let leftSyntax ← expandTerm scope left
      let rightSyntax ← expandTerm scope right
      `(Convertible $leftSyntax $rightSyntax)

end DeepWiki.Refine.CCOmega.SurfaceSyntax
