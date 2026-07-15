import DeepWiki.Refine.CCOmega.Typing

/-! # Named surface syntax for CCω

Readable named terms and contexts elaborate to the intrinsically scoped de Bruijn representation
used by the checked calculus core. `%{...}` interpolates an already scoped Lean value. -/

namespace DeepWiki.Refine.CCOmega.SurfaceSyntax

open DeepWiki.Refine.DependentCalculus
open Lean Macro

/-! The object-language grammar is
`A, B, t, u ::= □[i] | x | t u | λ x : A, t | Π x : A, B | %{e}`, with contexts
`Γ ::= ⟨⟩ | Γ, x : A | %{γ}`. -/

declare_syntax_cat ccwterm
syntax:max ident : ccwterm
syntax:max "□[" num "]" : ccwterm
syntax:max "(" ccwterm ")" : ccwterm
syntax:max "%{" term "}" : ccwterm
syntax:70 ccwterm:70 ccwterm:71 : ccwterm
syntax:25 ccwterm:26 " → " ccwterm:25 : ccwterm
syntax:20 "λ " ident " : " ccwterm ", " ccwterm : ccwterm
syntax:20 "Π " ident " : " ccwterm ", " ccwterm : ccwterm

declare_syntax_cat ccwctx
syntax:max "⟨⟩" : ccwctx
syntax:max "%{" term "}" : ccwctx
syntax:20 ccwctx ", " ident " : " ccwterm : ccwctx

/-- Find the de Bruijn index of the nearest binder carrying a surface name. -/
def nameIndex? (name : Name) : List Name → Option Nat
  | [] => none
  | current :: rest =>
      if name == current then some 0 else (nameIndex? name rest).map Nat.succ

/-- Tie an elaborated term's intrinsic scope to an elaborated context. -/
def inContext {n : Nat} (_context : Context n) (term : Term n) : Term n :=
  term

/-- Report whether a surface term contains an embedded Lean term. -/
partial def hasInterpolation (stx : Syntax) : Bool :=
  match stx with
  | `(ccwterm| %{ $_:term }) => true
  | `(ccwterm| ($term:ccwterm)) => hasInterpolation term
  | `(ccwterm| $function:ccwterm $argument:ccwterm) =>
      hasInterpolation function || hasInterpolation argument
  | `(ccwterm| $domain:ccwterm → $codomain:ccwterm) =>
      hasInterpolation domain || hasInterpolation codomain
  | `(ccwterm| λ $_:ident : $domain:ccwterm, $body:ccwterm) =>
      hasInterpolation domain || hasInterpolation body
  | `(ccwterm| Π $_:ident : $domain:ccwterm, $codomain:ccwterm) =>
      hasInterpolation domain || hasInterpolation codomain
  | _ => false

/-- Elaborate a named surface term into an intrinsically scoped `CCω` term. -/
partial def expandTerm (scope : List Name) (stx : Syntax) :
    MacroM (TSyntax `term) := do
  match stx with
  | `(ccwterm| %{ $term:term }) =>
      pure term
  | `(ccwterm| □[$level:num]) =>
      `(DeepWiki.Refine.DependentCalculus.Term.sort $level)
  | `(ccwterm| $name:ident) =>
      let some index := nameIndex? name.getId scope
        | Macro.throwErrorAt name s!"unbound CCω variable '{name.getId}'"
      let indexSyntax := quote index
      `(DeepWiki.Refine.DependentCalculus.Term.var $indexSyntax)
  | `(ccwterm| ($term:ccwterm)) =>
      expandTerm scope term
  | `(ccwterm| $function:ccwterm $argument:ccwterm) =>
      let functionSyntax ← expandTerm scope function
      let argumentSyntax ← expandTerm scope argument
      `(DeepWiki.Refine.DependentCalculus.Term.app $functionSyntax $argumentSyntax)
  | `(ccwterm| $domain:ccwterm → $codomain:ccwterm) =>
      let domainSyntax ← expandTerm scope domain
      let codomainSyntax ← expandTerm (Name.anonymous :: scope) codomain
      `(DeepWiki.Refine.DependentCalculus.Term.pi $domainSyntax $codomainSyntax)
  | `(ccwterm| λ $name:ident : $domain:ccwterm, $body:ccwterm) =>
      let domainSyntax ← expandTerm scope domain
      let bodySyntax ← expandTerm (name.getId :: scope) body
      `(DeepWiki.Refine.DependentCalculus.Term.lam $domainSyntax $bodySyntax)
  | `(ccwterm| Π $name:ident : $domain:ccwterm, $codomain:ccwterm) =>
      let domainSyntax ← expandTerm scope domain
      let codomainSyntax ← expandTerm (name.getId :: scope) codomain
      `(DeepWiki.Refine.DependentCalculus.Term.pi $domainSyntax $codomainSyntax)
  | _ => Macro.throwErrorAt stx "unsupported CCω term syntax"

/-- Elaborate a named dependent context and return its newest-first name scope. -/
partial def expandContext (stx : Syntax) :
    MacroM (List Name × TSyntax `term) := do
  match stx with
  | `(ccwctx| ⟨⟩) =>
      let emptySyntax ← `(DeepWiki.Refine.DependentCalculus.Context.empty)
      pure ([], emptySyntax)
  | `(ccwctx| %{ $context:term }) =>
      pure ([], context)
  | `(ccwctx| $context:ccwctx, $name:ident : $type:ccwterm) =>
      let (scope, contextSyntax) ← expandContext context
      if (nameIndex? name.getId scope).isSome then
        Macro.throwErrorAt name s!"duplicate CCω context variable '{name.getId}'"
      let typeSyntax ← expandTerm scope type
      let extendedSyntax ←
        `(DeepWiki.Refine.DependentCalculus.Context.extend $contextSyntax $typeSyntax)
      pure (name.getId :: scope, extendedSyntax)
  | _ => Macro.throwErrorAt stx "unsupported CCω context syntax"

/-- Elaborate a closed named term, or infer its ambient scope from an interpolation. -/
syntax:max "ccω!{" ccwterm "}" : term
macro_rules
  | `(ccω!{ $term:ccwterm }) => do
      let termSyntax ← expandTerm [] term
      if hasInterpolation term then
        `(($termSyntax : DeepWiki.Refine.DependentCalculus.Term _))
      else
        `(DeepWiki.Refine.CCOmega.SurfaceSyntax.inContext
          DeepWiki.Refine.DependentCalculus.Context.empty $termSyntax)

/-- Elaborate a named surface context to an indexed `Context`. -/
syntax:max "ccωctx!{" ccwctx "}" : term
macro_rules
  | `(ccωctx!{ $context:ccwctx }) => do
      let (_, contextSyntax) ← expandContext context
      `(($contextSyntax : DeepWiki.Refine.DependentCalculus.Context _))

/-- Elaborate an open named term relative to the displayed context. -/
syntax:max "ccωterm!{" ccwctx " ⊢ " ccwterm "}" : term
macro_rules
  | `(ccωterm!{ $context:ccwctx ⊢ $term:ccwterm }) => do
      let (scope, contextSyntax) ← expandContext context
      let termSyntax ← expandTerm scope term
      `(DeepWiki.Refine.CCOmega.SurfaceSyntax.inContext $contextSyntax $termSyntax)

/-- Elaborate a surface typing judgment directly to `HasType Γ t A`. -/
syntax:20 "ccω!{" ccwctx " ⊢ " ccwterm " : " ccwterm "}" : term
macro_rules
  | `(ccω!{ $context:ccwctx ⊢ $term:ccwterm : $type:ccwterm }) => do
      let (scope, contextSyntax) ← expandContext context
      let termSyntax ← expandTerm scope term
      let typeSyntax ← expandTerm scope type
      `(HasType $contextSyntax
        (DeepWiki.Refine.CCOmega.SurfaceSyntax.inContext $contextSyntax $termSyntax)
        (DeepWiki.Refine.CCOmega.SurfaceSyntax.inContext $contextSyntax $typeSyntax))

/-- Elaborate surface definitional equality to the core beta-convertibility relation. -/
syntax:20 "ccω!{" ccwctx " ⊢ " ccwterm " ≡ " ccwterm "}" : term
macro_rules
  | `(ccω!{ $context:ccwctx ⊢ $left:ccwterm ≡ $right:ccwterm }) => do
      let (scope, contextSyntax) ← expandContext context
      let leftSyntax ← expandTerm scope left
      let rightSyntax ← expandTerm scope right
      `(Convertible
        (DeepWiki.Refine.CCOmega.SurfaceSyntax.inContext $contextSyntax $leftSyntax)
        (DeepWiki.Refine.CCOmega.SurfaceSyntax.inContext $contextSyntax $rightSyntax))

end DeepWiki.Refine.CCOmega.SurfaceSyntax
