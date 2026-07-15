import DeepWiki.Refine.CCOmega.SurfaceSyntax
import DeepWiki.Refine.RawParametricitySyntax

/-! # Surface syntax for raw parametricity

Named `CCω` terms and contexts elaborate before applying the raw parametricity translations. -/

namespace DeepWiki.Refine.ParametricitySurfaceSyntax

open DeepWiki.Refine.CCOmega.SurfaceSyntax
open Lean Macro

/-- Elaborate a named term and apply the raw parametricity term translation. -/
syntax:max "rawω!{" ccwctx " ⊢ " ccwterm "}" : term
macro_rules
  | `(rawω!{ $context:ccwctx ⊢ $term:ccwterm }) => do
      let (scope, _) ← expandContext context
      let termSyntax ← expandTerm scope term
      `(DeepWiki.Refine.DependentCalculus.RawParametricity.translate $termSyntax)

/-- Elaborate a named context and apply the raw parametricity context translation. -/
syntax:max "rawωctx!{" ccwctx "}" : term
macro_rules
  | `(rawωctx!{ $context:ccwctx }) => do
      let (_, contextSyntax) ← expandContext context
      `(DeepWiki.Refine.DependentCalculus.RawParametricity.context $contextSyntax)

end DeepWiki.Refine.ParametricitySurfaceSyntax
