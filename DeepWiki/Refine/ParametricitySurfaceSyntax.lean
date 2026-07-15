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
      let (scope, contextSyntax) ← expandContext context
      let termSyntax ← expandTerm scope term
      `(DeepWiki.Refine.DependentCalculus.RawParametricity.translate
        (DeepWiki.Refine.CCOmega.SurfaceSyntax.inContext $contextSyntax $termSyntax))

/-- Elaborate a named context and apply the raw parametricity context translation. -/
syntax:max "rawωctx!{" ccwctx "}" : term
macro_rules
  | `(rawωctx!{ $context:ccwctx }) => do
      let (_, contextSyntax) ← expandContext context
      `(DeepWiki.Refine.DependentCalculus.RawParametricity.context $contextSyntax)

open DeepWiki.Refine.DependentCalculus

-- Translating the displayed empty context returns the empty context.
example : rawωctx!{ ⟨⟩ } = ccωctx!{ ⟨⟩ } :=
  rfl

-- Raw context notation accepts an intrinsically scoped Lean context.
example (source : Context n) :
    rawωctx!{ %{source} } =
      DeepWiki.Refine.DependentCalculus.RawParametricity.context source :=
  rfl

-- Raw term notation accepts a Lean term tied to its displayed Lean context.
example (source : Context n) (term : Term n) :
    rawω!{ %{source} ⊢ %{term} } =
      DeepWiki.Refine.DependentCalculus.RawParametricity.translate term :=
  rfl

-- A small type declaration expands to its original, primed, and relation-witness triple.
example :
    rawωctx!{ ⟨⟩, A : □[0] } =
      ccωctx!{ ⟨⟩,
        A0 : □[0],
        A1 : □[0],
        AR : (λ X : □[0], λ Y : □[0], X → Y → □[0]) A0 A1 } :=
  rfl

-- A universe becomes the type of heterogeneous relations.
example :
    rawω!{ ⟨⟩ ⊢ □[0] } =
      (ccω!{ λ A : □[0], λ B : □[0], A → B → □[0] } : Term 0) :=
  rfl

-- A source variable becomes its stored relation witness.
example :
    rawω!{ ⟨⟩, A : □[0] ⊢ A } =
      ccωterm!{ ⟨⟩,
        A0 : □[0],
        A1 : □[0],
        AR : (λ X : □[0], λ Y : □[0], X → Y → □[0]) A0 A1
        ⊢ AR } :=
  rfl

-- Application supplies the original, primed, and relational arguments.
example :
    rawω!{ ⟨⟩,
      A : □[0],
      f : A → A,
      x : A
      ⊢ f x } =
      ccωterm!{ ⟨⟩,
        A0 : □[0],
        A1 : □[0],
        AR : (λ X : □[0], λ Y : □[0], X → Y → □[0]) A0 A1,
        f0 : A0 → A0,
        f1 : A1 → A1,
        fR : Π a0 : A0, Π a1 : A1, AR a0 a1 → AR (f0 a0) (f1 a1),
        x0 : A0,
        x1 : A1,
        xR : AR x0 x1
        ⊢ fR x0 x1 xR } :=
  rfl

-- Lambda translation binds the original, primed, and relational inputs.
example :
    rawω!{ ⟨⟩ ⊢ λ A : □[0], A } =
      (ccω!{
        λ A0 : □[0],
        λ A1 : □[0],
        λ AR : (λ X : □[0], λ Y : □[0], X → Y → □[0]) A0 A1,
        AR } : Term 0) :=
  rfl

-- Related dependent functions map related inputs to related outputs.
example :
    rawω!{ ⟨⟩ ⊢ Π A : □[0], A } =
      (ccω!{
        λ f0 : Π A0 : □[0], A0,
        λ f1 : Π A1 : □[0], A1,
        Π A0 : □[0],
        Π A1 : □[0],
        Π AR : (λ X : □[0], λ Y : □[0], X → Y → □[0]) A0 A1,
        AR (f0 A0) (f1 A1) } : Term 0) :=
  rfl

end DeepWiki.Refine.ParametricitySurfaceSyntax
