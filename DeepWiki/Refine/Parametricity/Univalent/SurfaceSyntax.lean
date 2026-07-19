import DeepWiki.Refine.Parametricity.Univalent.Syntax

/-! # Named surface syntax for univalent parametricity

Readable named terms and contexts elaborate to the intrinsically scoped univalent-parametricity
syntax. `%{...}` interpolates an already scoped target-language term or context. -/

namespace DeepWiki.Refine.DependentCalculus.UnivalentParametricity.SurfaceSyntax

open Lean Macro
open DeepWiki.Refine.DependentCalculus.UnivalentParametricity

/-! The target-language grammar extends the core `CCω` forms with the package family `Pkg`,
the canonical universe package `p□`, dependent-product packages `pΠ`, and projection `rel`. -/

declare_syntax_cat uwterm
syntax:max ident : uwterm
syntax:max "□[" term "]" : uwterm
syntax:max "Pkg[" term "]" : uwterm
syntax:max "p□[" term "]" : uwterm
syntax:max "rel(" uwterm ")" : uwterm
syntax:max "(" uwterm ")" : uwterm
syntax:max "%{" term "}" : uwterm
syntax:70 uwterm:70 uwterm:71 : uwterm
syntax:25 uwterm:26 " → " uwterm:25 : uwterm
syntax:20 "λ " ident " : " uwterm ", " uwterm : uwterm
syntax:20 "Π " ident " : " uwterm ", " uwterm : uwterm
syntax:max "pΠ[" "(" ident " : " uwterm ")" " ↦ " uwterm
  ";" "(" ident " : " uwterm ")" " ↦ " uwterm
  ";" "(" ident " : " "rel(" uwterm ")" ident ident ")" " ↦ " uwterm "]" : uwterm

declare_syntax_cat uwctx
syntax:max "⟨⟩" : uwctx
syntax:max "%{" term "}" : uwctx
syntax:20 uwctx ", " ident " : " uwterm : uwctx

/-- Find the de Bruijn index of the nearest binder carrying a surface name. -/
def nameIndex? (name : Name) : List Name → Option Nat
  | [] => none
  | current :: rest =>
      if name == current then some 0 else (nameIndex? name rest).map Nat.succ

/-- Tie an elaborated target-language term's intrinsic scope to an elaborated context. -/
def inContext {n : Nat} (_context : Context n) (term : Term n) : Term n :=
  term

/-- Report whether a surface term contains an embedded target-language term. -/
partial def hasInterpolation (stx : Syntax) : Bool :=
  match stx with
  | `(uwterm| %{ $_:term }) => true
  | `(uwterm| rel($package:uwterm)) => hasInterpolation package
  | `(uwterm| ($term:uwterm)) => hasInterpolation term
  | `(uwterm| $function:uwterm $argument:uwterm) =>
      hasInterpolation function || hasInterpolation argument
  | `(uwterm| $domain:uwterm → $codomain:uwterm) =>
      hasInterpolation domain || hasInterpolation codomain
  | `(uwterm| λ $_:ident : $domain:uwterm, $body:uwterm) =>
      hasInterpolation domain || hasInterpolation body
  | `(uwterm| Π $_:ident : $domain:uwterm, $codomain:uwterm) =>
      hasInterpolation domain || hasInterpolation codomain
  | `(uwterm|
      pΠ[($_:ident : $leftDomain:uwterm) ↦ $leftCodomain:uwterm;
        ($_:ident : $rightDomain:uwterm) ↦ $rightCodomain:uwterm;
        ($_:ident : rel($domainPackage:uwterm) $_:ident $_:ident) ↦
          $codomainPackage:uwterm]) =>
      hasInterpolation leftDomain || hasInterpolation rightDomain ||
        hasInterpolation leftCodomain || hasInterpolation rightCodomain ||
        hasInterpolation domainPackage || hasInterpolation codomainPackage
  | _ => false

/-- Elaborate a named surface term into an intrinsically scoped univalent-parametricity term. -/
partial def expandTerm (scope : List Name) (stx : Syntax) :
    MacroM (TSyntax `term) := do
  match stx with
  | `(uwterm| %{ $term:term }) =>
      pure term
  | `(uwterm| □[$level:term]) =>
      `(DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Term.sort $level)
  | `(uwterm| Pkg[$level:term]) =>
      `(DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Term.packageFamily $level)
  | `(uwterm| p□[$level:term]) =>
      `(DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Term.universePackage $level)
  | `(uwterm| rel($package:uwterm)) =>
      let packageSyntax ← expandTerm scope package
      `(DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Term.relationProjection
        $packageSyntax)
  | `(uwterm| $name:ident) =>
      let some index := nameIndex? name.getId scope
        | Macro.throwErrorAt name s!"unbound univalent-parametricity variable '{name.getId}'"
      let indexSyntax := quote index
      `(DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Term.var $indexSyntax)
  | `(uwterm| ($term:uwterm)) =>
      expandTerm scope term
  | `(uwterm| $function:uwterm $argument:uwterm) =>
      let functionSyntax ← expandTerm scope function
      let argumentSyntax ← expandTerm scope argument
      `(DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Term.app
        $functionSyntax $argumentSyntax)
  | `(uwterm| $domain:uwterm → $codomain:uwterm) =>
      let domainSyntax ← expandTerm scope domain
      let codomainSyntax ← expandTerm (Name.anonymous :: scope) codomain
      `(DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Term.pi
        $domainSyntax $codomainSyntax)
  | `(uwterm| λ $name:ident : $domain:uwterm, $body:uwterm) =>
      let domainSyntax ← expandTerm scope domain
      let bodySyntax ← expandTerm (name.getId :: scope) body
      `(DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Term.lam
        $domainSyntax $bodySyntax)
  | `(uwterm| Π $name:ident : $domain:uwterm, $codomain:uwterm) =>
      let domainSyntax ← expandTerm scope domain
      let codomainSyntax ← expandTerm (name.getId :: scope) codomain
      `(DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Term.pi
        $domainSyntax $codomainSyntax)
  | `(uwterm|
      pΠ[($leftName:ident : $leftDomain:uwterm) ↦ $leftCodomain:uwterm;
        ($rightName:ident : $rightDomain:uwterm) ↦ $rightCodomain:uwterm;
        ($relationName:ident : rel($domainPackage:uwterm)
          $relationLeft:ident $relationRight:ident) ↦ $codomainPackage:uwterm]) =>
      if leftName.getId == rightName.getId then
        Macro.throwErrorAt rightName s!"duplicate pΠ binder '{rightName.getId}'"
      if leftName.getId == relationName.getId then
        Macro.throwErrorAt relationName s!"duplicate pΠ binder '{relationName.getId}'"
      if rightName.getId == relationName.getId then
        Macro.throwErrorAt relationName s!"duplicate pΠ binder '{relationName.getId}'"
      unless relationLeft.getId == leftName.getId do
        Macro.throwErrorAt relationLeft
          s!"pΠ relation must first apply to '{leftName.getId}'"
      unless relationRight.getId == rightName.getId do
        Macro.throwErrorAt relationRight
          s!"pΠ relation must second apply to '{rightName.getId}'"
      let leftDomainSyntax ← expandTerm scope leftDomain
      let rightDomainSyntax ← expandTerm scope rightDomain
      let leftCodomainSyntax ← expandTerm (leftName.getId :: scope) leftCodomain
      let rightCodomainSyntax ← expandTerm (rightName.getId :: scope) rightCodomain
      let domainPackageSyntax ← expandTerm scope domainPackage
      let codomainPackageSyntax ← expandTerm
        (relationName.getId :: rightName.getId :: leftName.getId :: scope)
        codomainPackage
      `(DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Term.dependentProductPackage
        $leftDomainSyntax $rightDomainSyntax $leftCodomainSyntax $rightCodomainSyntax
        $domainPackageSyntax $codomainPackageSyntax)
  | _ => Macro.throwErrorAt stx "unsupported univalent-parametricity term syntax"

/-- Elaborate a named target-language context and return its newest-first name scope. -/
partial def expandContext (stx : Syntax) :
    MacroM (List Name × TSyntax `term) := do
  match stx with
  | `(uwctx| ⟨⟩) =>
      let emptySyntax ←
        `(DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Context.empty)
      pure ([], emptySyntax)
  | `(uwctx| %{ $context:term }) =>
      pure ([], context)
  | `(uwctx| $context:uwctx, $name:ident : $type:uwterm) =>
      let (scope, contextSyntax) ← expandContext context
      if (nameIndex? name.getId scope).isSome then
        Macro.throwErrorAt name
          s!"duplicate univalent-parametricity context variable '{name.getId}'"
      let typeSyntax ← expandTerm scope type
      let extendedSyntax ←
        `(DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Context.extend
          $contextSyntax $typeSyntax)
      pure (name.getId :: scope, extendedSyntax)
  | _ => Macro.throwErrorAt stx "unsupported univalent-parametricity context syntax"

/-- Elaborate a closed named target-language term, or infer its scope from an interpolation. -/
syntax:max "uω!{" uwterm "}" : term
macro_rules
  | `(uω!{ $term:uwterm }) => do
      let termSyntax ← expandTerm [] term
      if hasInterpolation term then
        `(($termSyntax : DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Term _))
      else
        `(DeepWiki.Refine.DependentCalculus.UnivalentParametricity.SurfaceSyntax.inContext
          DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Context.empty $termSyntax)

/-- Elaborate a named target-language context to an indexed extended `Context`. -/
syntax:max "uωctx!{" uwctx "}" : term
macro_rules
  | `(uωctx!{ $context:uwctx }) => do
      let (_, contextSyntax) ← expandContext context
      `(($contextSyntax : DeepWiki.Refine.DependentCalculus.UnivalentParametricity.Context _))

/-- Elaborate an open named target-language term relative to the displayed context. -/
syntax:max "uωterm!{" uwctx " ⊢ " uwterm "}" : term
macro_rules
  | `(uωterm!{ $context:uwctx ⊢ $term:uwterm }) => do
      let (scope, contextSyntax) ← expandContext context
      let termSyntax ← expandTerm scope term
      `(DeepWiki.Refine.DependentCalculus.UnivalentParametricity.SurfaceSyntax.inContext
        $contextSyntax $termSyntax)

example (level : Nat) :
    (uω!{ p□[level + 1] } : Term 0) = .universePackage (level + 1) :=
  rfl

example (level : Nat) :
    (uω!{ Pkg[level] } : Term 0) = .packageFamily level :=
  rfl

example (package : Term n) :
    uω!{ rel(%{package}) } = .relationProjection package :=
  rfl

example :
    (uω!{
      pΠ[(x0 : □[0]) ↦ x0;
        (x1 : □[0]) ↦ x1;
        (xR : rel(p□[0]) x0 x1) ↦ xR x0 x1] } : Term 0) =
      .dependentProductPackage (.sort 0) (.sort 0) (.var 0) (.var 0)
        (.universePackage 0) (.app (.app (.var 0) (.var 2)) (.var 1)) :=
  rfl

example :
    uωterm!{ ⟨⟩, A : □[0], x : A ⊢ x } = (.var 0 : Term 2) :=
  rfl

end DeepWiki.Refine.DependentCalculus.UnivalentParametricity.SurfaceSyntax
