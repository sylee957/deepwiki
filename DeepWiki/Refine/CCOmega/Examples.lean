import DeepWiki.Refine.CCOmega.SurfaceSyntax

/-! # Reading CCω terms and typing derivations

This guide introduces the general term grammar, dependent contexts, and each ordinary typing rule
before the calculus is used by a translation. Named notation keeps the examples readable, while
every statement elaborates to the intrinsically scoped `Term`, `Context`, and `HasType` core. -/

namespace DeepWiki.Refine.CCOmega.Examples

open DeepWiki.Refine.DependentCalculus

universe u

/-! ## General terms

A `Term n` is a term with exactly `n` free-variable positions available. Its five constructors are:

* `.sort i` for the universe `□[i]`;
* `.var k` for the variable at de Bruijn index `k : Fin n`;
* `.app f x` for application `f x`;
* `.lam A t` for a lambda `λ x : A, t` whose body has one additional variable;
* `.pi A B` for a dependent function type `Π x : A, B`, again with one additional variable in
  the codomain.

The index prevents dangling variables but does not itself prove that a term has a type. For
example, both a universe and an application of two universes are closed `Term 0` values, although
only the former has an ordinary `CCω` typing derivation.
-/

-- A universe elaborates to `.sort`.
example : (ccω!{ □[0] } : Term 0) = .sort 0 := rfl

-- A named free variable elaborates to its de Bruijn index.
example : ccωterm!{ ⟨⟩, A : □[0] ⊢ A } = (.var 0 : Term 1) := rfl

-- Application elaborates to `.app`.
example :
    (ccω!{ (λ A : □[1], A) □[0] } : Term 0) =
      .app (.lam (.sort 1) (.var 0)) (.sort 0) :=
  rfl

-- A lambda elaborates to `.lam`, with its bound variable at index zero.
example :
    (ccω!{ λ A : □[0], A } : Term 0) = .lam (.sort 0) (.var 0) :=
  rfl

-- A dependent product elaborates to `.pi`.
example :
    (ccω!{ Π A : □[0], A } : Term 0) = .pi (.sort 0) (.var 0) :=
  rfl

-- Nested binders increment the available de Bruijn positions.
example :
    (ccω!{ λ A : □[0], λ x : A, x } : Term 0) =
      .lam (.sort 0) (.lam (.var 0) (.var 0)) :=
  rfl

/-! ## Lean interpolation

`%{value}` inserts an already elaborated Lean `Term n` or `Context n` into the readable
object-language syntax. The inserted term must already have exactly the scope at the insertion
point; interpolation does not weaken or otherwise rewrite it.
-/

-- A Lean term can be inserted directly into a surface term.
example (term : Term n) : ccω!{ %{term} } = term := rfl

-- Without an interpolation, standalone term notation still denotes a closed term.
example :
    (let identity := ccω!{ λ A : □[0], A }; identity) =
      (.lam (.sort 0) (.var 0) : Term 0) :=
  rfl

-- Several inserted Lean terms can be combined with object-language application syntax.
example (function argument : Term n) :
    ccω!{ %{function} %{argument} } = .app function argument :=
  rfl

-- A Lean context can be continued using named object-language declarations.
example (source : Context n) (type : Term n) :
    ccωctx!{ %{source}, x : %{type} } = .extend source type :=
  rfl

-- Names introduced after an opaque Lean context still elaborate to de Bruijn indices.
example (source : Context n) (type : Term n) :
    ccωterm!{ %{source}, x : %{type} ⊢ x } = (.var 0 : Term (n + 1)) :=
  rfl

-- An inserted body already lives under the binder introduced by the surface lambda.
example (domain : Term n) (body : Term (n + 1)) :
    ccω!{ λ x : %{domain}, %{body} } = .lam domain body :=
  rfl

-- Context-bearing typing notation checks every interpolation against the displayed scope.
example (source : Context n) (term type : Term n)
    (typing : HasType source term type) :
    ccω!{ %{source} ⊢ %{term} : %{type} } :=
  typing

-- Context-bearing convertibility likewise requires two terms in that same scope.
example (source : Context n) (left right : Term n)
    (conversion : Convertible left right) :
    ccω!{ %{source} ⊢ %{left} ≡ %{right} } :=
  conversion

/-! ## Contexts

Read `⟨⟩, A : □[0], x : A` from left to right. The empty context assumes nothing,
`A : □[0]` introduces a small type, and `x : A` introduces a value whose type refers to `A`.
A raw `Context n` guarantees scoping; `WellFormed Γ` additionally proves that each declaration is
itself typed by some universe.
-/

/-- The one-declaration context containing a small type `A`. -/
def typeContext : Context 1 :=
  ccωctx!{ ⟨⟩, A : □[0] }

/-- The context `A : □[0]` is well formed. -/
theorem typeContextWellFormed : WellFormed typeContext :=
  .extend .empty (.sort .empty 0)

/-- The dependent context containing a small type `A` and a value `x : A`. -/
def typeValueContext : Context 2 :=
  ccωctx!{ ⟨⟩, A : □[0], x : A }

/-- The context `A : □[0], x : A` is well formed. -/
theorem typeValueContextWellFormed : WellFormed typeValueContext :=
  .extend typeContextWellFormed (.var typeContextWellFormed 0)

/-- Named context notation elaborates to newest-first de Bruijn declarations. -/
theorem typeValueContext_expansion :
    typeValueContext = .extend (.extend .empty (.sort 0)) (.var 0) :=
  rfl

/-! ## Typing rules

`HasType Γ t A` is the Lean form of `Γ ⊢ t : A`. It is evidence, not a Boolean checker: a
derivation is built from the universe, variable, application, lambda, dependent-product,
conversion, and cumulativity rules below.

### Universes and variables

The universe rule gives `□[i] : □[i+1]`. The variable rule obtains a variable's dependent type
by looking it up in a well-formed context.
-/

/-- The lowest universe is an element of its successor universe. -/
theorem universeTypingExample : ccω!{ ⟨⟩ ⊢ □[0] : □[1] } :=
  .sort .empty 0

/-- Looking up `A` in its context proves `A : □[0]`. -/
theorem typeVariableTypingExample : ccω!{ ⟨⟩, A : □[0] ⊢ A : □[0] } :=
  .var typeContextWellFormed 0

/-- Looking up the newest declaration proves `x : A`. -/
theorem valueVariableTypingExample :
    ccω!{ ⟨⟩, A : □[0], x : A ⊢ x : A } :=
  .var typeValueContextWellFormed 0

/-! ### Dependent products and lambdas

The product rule checks the domain in the current context and the codomain after extending the
context by that domain. The lambda rule uses the same extended context to check its body, then
assigns the resulting dependent-product type to the abstraction.
-/

/-- The polymorphic identity's dependent-product type belongs to `□[1]`. -/
theorem polymorphicIdentityTypeTypingExample :
    ccω!{ ⟨⟩ ⊢ Π A : □[0], Π x : A, A : □[1] } := by
  exact .pi (.sort .empty 0)
    (.pi (.var typeContextWellFormed 0) (.var typeValueContextWellFormed 1))

/-- The polymorphic identity has its dependent-product type. -/
theorem polymorphicIdentityTypingExample :
    ccω!{ ⟨⟩ ⊢
      λ A : □[0], λ x : A, x :
      Π A : □[0], Π x : A, A } := by
  exact .lam (.sort .empty 0)
    (.lam (.var typeContextWellFormed 0) (.var typeValueContextWellFormed 0))

/-! ### Application

If `f` has type `Π x : A, B` and `u` has type `A`, the application rule gives `f u` the type
obtained by substituting `u` for the newest variable in `B`.
-/

/-- Applying the local identity to `x` is a well-scoped `CCω` term. -/
def localIdentityApplication : Term 2 :=
  ccωterm!{ ⟨⟩, A : □[0], x : A ⊢ (λ y : A, y) x }

/-- The beta-normal result of applying the local identity to `x`. -/
def localIdentityResult : Term 2 :=
  ccωterm!{ ⟨⟩, A : □[0], x : A ⊢ x }

/-- Beta reduction substitutes `x` for `y` in the local identity body. -/
theorem localIdentityBetaExample :
    BetaStep localIdentityApplication localIdentityResult :=
  .beta _ _ _

/-- The application rule proves that the local identity applied to `x` has type `A`. -/
theorem localIdentityApplicationTypingExample :
    ccω!{ ⟨⟩, A : □[0], x : A ⊢ (λ y : A, y) x : A } := by
  let aWellTyped := HasType.var typeValueContextWellFormed (1 : Fin 2)
  let bodyContextWellFormed := WellFormed.extend typeValueContextWellFormed aWellTyped
  let bodyWellTyped := HasType.var bodyContextWellFormed (0 : Fin 3)
  let functionWellTyped := HasType.lam aWellTyped bodyWellTyped
  let argumentWellTyped := HasType.var typeValueContextWellFormed (0 : Fin 2)
  exact HasType.app functionWellTyped argumentWellTyped

/-! ### Conversion and cumulativity

Conversion changes a term's type along beta-convertibility. Cumulativity instead raises a type
along the universe hierarchy, so a term accepted at a smaller universe remains accepted at a
larger compatible one.
-/

/-- Cumulativity regards `□[0]` as an element of the still higher universe `□[2]`. -/
theorem universeCumulativityExample : ccω!{ ⟨⟩ ⊢ □[0] : □[2] } :=
  HasType.sort_of_lt .empty (by decide)

/-- Conversion accepts a beta-expanded presentation of the type `A`. -/
theorem conversionTypingExample :
    ccω!{ ⟨⟩, A : □[0], x : A ⊢ x : (λ X : □[0], X) A } := by
  let targetDomainWellTyped := HasType.sort typeValueContextWellFormed 0
  let targetBodyContextWellFormed :=
    WellFormed.extend typeValueContextWellFormed targetDomainWellTyped
  let targetBodyWellTyped := HasType.var targetBodyContextWellFormed (0 : Fin 3)
  let targetFunctionWellTyped := HasType.lam targetDomainWellTyped targetBodyWellTyped
  let aWellTyped := HasType.var typeValueContextWellFormed (1 : Fin 2)
  let targetWellTyped := HasType.app targetFunctionWellTyped aWellTyped
  let xWellTyped := HasType.var typeValueContextWellFormed (0 : Fin 2)
  change HasType typeValueContext (.var 0) (.var 1) at xWellTyped
  have targetToSource :
      Convertible
        (.app (.lam (.sort 0) (.var 0)) (.var 1) : Term 2)
        (.var 1) :=
    .beta (.beta _ _ _)
  exact HasType.conversion xWellTyped targetWellTyped targetToSource.symm

end DeepWiki.Refine.CCOmega.Examples
