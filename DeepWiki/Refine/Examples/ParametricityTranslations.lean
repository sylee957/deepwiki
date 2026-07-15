import DeepWiki.Refine.ParametricityTranslations
import DeepWiki.Refine.RawParametricityTyping

/-! # Reading parametricity translations through `CCω`

This tutorial starts with the syntax and typing judgment of a small Calculus of Constructions,
then explains raw and univalent parametricity as translations of that syntax.

The notation macros accept named mathematical terms such as `λ x : A, x` and elaborate them to the
intrinsically scoped de Bruijn representation used by the checked core. Thus the names are for the
reader, while all examples are proofs about the actual `Term`, `Context`, and `HasType` definitions.
-/

namespace DeepWiki.Refine.ParametricityTranslationTutorial

open DeepWiki.Refine.DependentCalculus
open DeepWiki.Refine.DependentCalculus.RawParametricity
open Lean Macro

universe u

/-! ## Named surface notation

The object language has the grammar

`A, B, t, u ::= □[i] | x | t u | λ x : A, t | Π x : A, B`.

A context has the grammar `Γ ::= ⟨⟩ | Γ, x : A`. The wrappers `ccω!{...}` and
`ccωctx!{...}` only tell Lean where this object-language syntax begins and ends.
-/

declare_syntax_cat ccwterm
syntax:max ident : ccwterm
syntax:max "□[" num "]" : ccwterm
syntax:max "□₀" : ccwterm
syntax:max "□₁" : ccwterm
syntax:max "□₂" : ccwterm
syntax:max "(" ccwterm ")" : ccwterm
syntax:70 ccwterm:70 ccwterm:71 : ccwterm
syntax:25 ccwterm:26 " → " ccwterm:25 : ccwterm
syntax:20 "λ " ident " : " ccwterm ", " ccwterm : ccwterm
syntax:20 "Π " ident " : " ccwterm ", " ccwterm : ccwterm

declare_syntax_cat ccwctx
syntax:max "⟨⟩" : ccwctx
syntax:20 ccwctx ", " ident " : " ccwterm : ccwctx

/-- Find the de Bruijn index of the nearest binder carrying a surface name. -/
private def nameIndex? (name : Name) : List Name → Option Nat
  | [] => none
  | current :: rest =>
      if name == current then some 0 else (nameIndex? name rest).map Nat.succ

/-- Elaborate a named surface term into an intrinsically scoped `CCω` term. -/
private partial def expandTerm (scope : List Name) (stx : Syntax) :
    MacroM (TSyntax `term) := do
  match stx with
  | `(ccwterm| □₀) =>
      `(.sort 0)
  | `(ccwterm| □₁) =>
      `(.sort 1)
  | `(ccwterm| □₂) =>
      `(.sort 2)
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
private partial def expandContext (stx : Syntax) :
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

-- A closed surface term elaborates to `Term 0`.
syntax:max "ccω!{" ccwterm "}" : term
macro_rules
  | `(ccω!{ $term:ccwterm }) => do
      return (← expandTerm [] term).raw

-- A surface context elaborates to the indexed `Context` type.
syntax:max "ccωctx!{" ccwctx "}" : term
macro_rules
  | `(ccωctx!{ $context:ccwctx }) => do
      let (_, contextSyntax) ← expandContext context
      pure contextSyntax.raw

-- An open term is elaborated relative to the declarations displayed before `⊢`.
syntax:max "ccωterm!{" ccwctx " ⊢ " ccwterm "}" : term
macro_rules
  | `(ccωterm!{ $context:ccwctx ⊢ $term:ccwterm }) => do
      let (scope, _) ← expandContext context
      return (← expandTerm scope term).raw

-- A surface typing judgment elaborates directly to `HasType Γ t A`.
syntax:20 "ccω!{" ccwctx " ⊢ " ccwterm " : " ccwterm "}" : term
macro_rules
  | `(ccω!{ $context:ccwctx ⊢ $term:ccwterm : $type:ccwterm }) => do
      let (scope, contextSyntax) ← expandContext context
      let termSyntax ← expandTerm scope term
      let typeSyntax ← expandTerm scope type
      `(HasType $contextSyntax $termSyntax $typeSyntax)

-- Definitional equality elaborates to the checked core's beta-convertibility relation.
syntax:20 "ccω!{" ccwctx " ⊢ " ccwterm " ≡ " ccwterm "}" : term
macro_rules
  | `(ccω!{ $context:ccwctx ⊢ $left:ccwterm ≡ $right:ccwterm }) => do
      let (scope, _) ← expandContext context
      let leftSyntax ← expandTerm scope left
      let rightSyntax ← expandTerm scope right
      `(Convertible $leftSyntax $rightSyntax)

-- These two wrappers apply the raw term and context translations after surface elaboration.
syntax:max "rawω!{" ccwctx " ⊢ " ccwterm "}" : term
macro_rules
  | `(rawω!{ $context:ccwctx ⊢ $term:ccwterm }) => do
      let (scope, _) ← expandContext context
      let termSyntax ← expandTerm scope term
      `(DeepWiki.Refine.DependentCalculus.RawParametricity.translate $termSyntax)

syntax:max "rawωctx!{" ccwctx "}" : term
macro_rules
  | `(rawωctx!{ $context:ccwctx }) => do
      let (_, contextSyntax) ← expandContext context
      `(DeepWiki.Refine.DependentCalculus.RawParametricity.context $contextSyntax)

/-! ## What a context is

Read `⟨⟩, A : □₀, x : A` from left to right:

* `⟨⟩` says that nothing has been assumed yet.
* `A : □₀` introduces a variable `A` whose value is a small type.
* `x : A` introduces a value `x`; its type may refer to the earlier declaration `A`.

Thus a context is the ordered list of declarations available while checking the expression to the
right of `⊢`. It is not itself a relation and is not the earlier tutorial's `Related` record.
-/

/-- The one-declaration context containing a small type `A`. -/
def typeContext : Context 1 :=
  ccωctx!{ ⟨⟩, A : □₀ }

/-- The context `A : □₀` is well formed. -/
def typeContextWellFormed : WellFormed typeContext :=
  .extend .empty (.sort .empty 0)

/-- The dependent context containing a small type `A` and a value `x : A`. -/
def typeValueContext : Context 2 :=
  ccωctx!{ ⟨⟩, A : □₀, x : A }

/-- The context `A : □₀, x : A` is well formed. -/
def typeValueContextWellFormed : WellFormed typeValueContext :=
  .extend typeContextWellFormed (.var typeContextWellFormed 0)

/-- The named context macro elaborates `A` and `x` to the expected de Bruijn declarations. -/
theorem typeValueContext_expansion :
    typeValueContext = .extend (.extend .empty (.sort 0)) (.var 0) :=
  rfl

/-! ## The ordinary `CCω` typing rules

`HasType Γ t A` is the Lean form of `Γ ⊢ t : A`. Its constructors are the inference rules for a
universe, a variable, application, lambda abstraction, dependent products, conversion, and
cumulativity. The following small derivations exercise those rules directly.
-/

/-- The lowest universe is an element of its successor universe. -/
theorem universeTypingExample : ccω!{ ⟨⟩ ⊢ □₀ : □₁ } :=
  .sort .empty 0

/-- Looking up `A` in its context proves `A : □₀`. -/
theorem typeVariableTypingExample : ccω!{ ⟨⟩, A : □₀ ⊢ A : □₀ } :=
  .var typeContextWellFormed 0

/-- Looking up the newest declaration proves `x : A`. -/
theorem valueVariableTypingExample :
    ccω!{ ⟨⟩, A : □₀, x : A ⊢ x : A } :=
  .var typeValueContextWellFormed 0

/-- The polymorphic identity's dependent-product type belongs to `□₁`. -/
theorem polymorphicIdentityTypeTypingExample :
    ccω!{ ⟨⟩ ⊢ Π A : □₀, Π x : A, A : □₁ } := by
  exact .pi (.sort .empty 0)
    (.pi (.var typeContextWellFormed 0) (.var typeValueContextWellFormed 1))

/-- The named term `λ A, λ x, x` has the polymorphic identity type. -/
theorem polymorphicIdentityTypingExample :
    ccω!{ ⟨⟩ ⊢
      λ A : □₀, λ x : A, x :
      Π A : □₀, Π x : A, A } := by
  exact .lam (.sort .empty 0)
    (.lam (.var typeContextWellFormed 0) (.var typeValueContextWellFormed 0))

/-- Applying the local identity to `x` is a well-scoped `CCω` term. -/
def localIdentityApplication : Term 2 :=
  ccωterm!{ ⟨⟩, A : □₀, x : A ⊢ (λ y : A, y) x }

/-- The beta-normal result of applying the local identity to `x`. -/
def localIdentityResult : Term 2 :=
  ccωterm!{ ⟨⟩, A : □₀, x : A ⊢ x }

/-- Beta reduction substitutes `x` for `y` in the local identity body. -/
theorem localIdentityBetaExample :
    BetaStep localIdentityApplication localIdentityResult :=
  .beta _ _ _

/-- The application rule proves that the local identity applied to `x` has type `A`. -/
theorem localIdentityApplicationTypingExample :
    ccω!{ ⟨⟩, A : □₀, x : A ⊢ (λ y : A, y) x : A } := by
  let aWellTyped := HasType.var typeValueContextWellFormed (1 : Fin 2)
  let bodyContextWellFormed := WellFormed.extend typeValueContextWellFormed aWellTyped
  let bodyWellTyped := HasType.var bodyContextWellFormed (0 : Fin 3)
  let functionWellTyped := HasType.lam aWellTyped bodyWellTyped
  let argumentWellTyped := HasType.var typeValueContextWellFormed (0 : Fin 2)
  exact HasType.app functionWellTyped argumentWellTyped

/-- Cumulativity also regards `□₀` as an element of the still higher universe `□₂`. -/
theorem universeCumulativityExample : ccω!{ ⟨⟩ ⊢ □₀ : □₂ } :=
  HasType.sort_of_lt .empty (by decide)

/-- The conversion rule accepts a beta-expanded presentation of the type `A`. -/
theorem conversionTypingExample :
    ccω!{ ⟨⟩, A : □₀, x : A ⊢ x : (λ X : □₀, X) A } := by
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

/-! ## Raw context translation

Raw parametricity simultaneously studies three versions of each source expression:

* `t` is the original expression, renamed into the translated context.
* `t′` is a fresh primed copy.
* `⟦t⟧` is evidence that `t` and `t′` are related.

Consequently, one source declaration `x : A` becomes three target declarations:

`x : A, x′ : A′, xᴿ : ⟦A⟧ x x′`.

For `A : □₀, x : A`, the whole translated context is therefore ordered as
`A, A′, Aᴿ, x, x′, xᴿ`. Because the kernel uses newest-first de Bruijn indices, the last three have
indices `xᴿ = 0`, `x′ = 1`, and `x = 2`.
-/

/-- Translating `A : □₀` produces a context containing the triple `A, A′, Aᴿ`. -/
def translatedTypeContext : Context 3 :=
  rawωctx!{ ⟨⟩, A : □₀ }

/-- The translated one-type context is well formed. -/
def translatedTypeContextWellFormed : WellFormed translatedTypeContext :=
  context_extend_wellFormed context_empty_wellFormed
    (.sort .empty 0)
    (translate_sort_witness_hasType context_empty_wellFormed 0)

/-- Translating `A : □₀, x : A` produces six dependent declarations. -/
def translatedTypeValueContext : Context 6 :=
  rawωctx!{ ⟨⟩, A : □₀, x : A }

/-- The translated type-and-value context is well formed. -/
def translatedTypeValueContextWellFormed : WellFormed translatedTypeValueContext :=
  context_extend_wellFormed translatedTypeContextWellFormed
    (.var typeContextWellFormed 0)
    (translate_var_witness_hasType translatedTypeContextWellFormed 0)

/-- The translated context stores `x`, `x′`, and `xᴿ` at indices two, one, and zero. -/
theorem translatedNewestTripleLayout :
    (originalRenaming 2 0).val = 2 ∧
      (primedRenaming 2 0).val = 1 ∧
      (witnessRenaming 2 0).val = 0 := by
  decide

/-- The source variable `x` in the example context. -/
def sourceX : Term 2 :=
  ccωterm!{ ⟨⟩, A : □₀, x : A ⊢ x }

/-- The original copy of `x` selects the original slot of its translated triple. -/
theorem sourceX_original : original sourceX = .var (originalRenaming 2 0) :=
  rfl

/-- The primed copy of `x` selects the primed slot of its translated triple. -/
theorem sourceX_primed : primed sourceX = .var (primedRenaming 2 0) :=
  rfl

/-- Translating the variable `x` selects its stored relation witness `xᴿ`. -/
theorem sourceX_translation : translate sourceX = .var (witnessRenaming 2 0) :=
  rfl

/-- The stored witness `xᴿ` has exactly the translated relation type for `x`. -/
theorem sourceX_translation_hasType :
    HasType translatedTypeValueContext (translate sourceX)
      (relatedTermType sourceX (typeValueContext.lookup 0)) :=
  translate_var_witness_hasType translatedTypeValueContextWellFormed 0

/-! ## Raw term translation

The remaining clauses are structural:

* A universe becomes the type of heterogeneous relations between two types.
* Application feeds the original argument, the primed argument, and their witness to the
  translated function.
* Lambda translation binds an original input, a primed input, and their witness.
* Product translation says that related functions map related inputs to related outputs.

The general checked equations are `translate_sort`, `translate_var`, `translate_app`,
`translate_lam`, and `translate_pi`.
-/

/-- Raw application consumes the original argument, its primed copy, and its witness. -/
theorem applicationTranslationRuleExample (function argument : Term n) :
    translate (.app function argument) =
      .app (.app (.app (translate function) (original argument)) (primed argument))
        (translate argument) :=
  translate_app function argument

/-- The universe translation satisfies its displayed typing equation in the empty context. -/
theorem rawUniverseTypingExample (level : Nat) :
    HasType Context.empty (translate (.sort level : Term 0))
      (.app
        (.app (translate (.sort (level + 1) : Term 0)) (.sort level))
        (.sort level)) :=
  rawUniverseTranslation_hasType level

/-! ## The same product rule as an ordinary Lean proof

The syntax translation above generates a proof obligation. After interpreting the source and target
types as actual Lean types, that obligation is just a function which accepts two inputs and evidence
that they are related, then returns evidence that the outputs are related.
-/

/-- A second representation of a natural number. -/
structure BoxedNat where
  /-- The represented natural number. -/
  value : Nat

/-- Successor in the boxed representation. -/
def boxedSucc (number : BoxedNat) : BoxedNat :=
  ⟨Nat.succ number.value⟩

/-- Boxing and unboxing form an equivalence of natural-number representations. -/
def natBoxedEquivalence : Nat ≃ BoxedNat where
  toFun := fun number => ⟨number⟩
  invFun := BoxedNat.value
  left_inv := fun _ => rfl
  right_inv := fun boxed => by
    cases boxed
    rfl

/-- The equality graph of boxing gives a univalent relation between the representations. -/
def natBoxedRelation : UnivalentRelation Nat BoxedNat :=
  UnivalentRelation.ofEquiv natBoxedEquivalence

/-- Unary two and boxed two are related by the equality graph of unboxing. -/
def twoRelated : natBoxedRelation.rel 2 ⟨2⟩ :=
  ⟨⟨rfl⟩⟩

/-- Unary and boxed successor map related inputs to related outputs. -/
def successorRelated :
    RawPiRelation natBoxedRelation.rel (fun _ _ _ => natBoxedRelation.rel)
      Nat.succ boxedSucc :=
  fun _ _ related => ⟨⟨congrArg Nat.succ related.down.down⟩⟩

/-- Applying the related successors to related twos produces related threes. -/
def successorApplicationExample :
    natBoxedRelation.rel (Nat.succ 2) (boxedSucc ⟨2⟩) :=
  successorRelated 2 ⟨2⟩ twoRelated

/-! ## Why univalent parametricity is narrower

Raw universe translation permits any heterogeneous relation. Univalent translation instead packages
a relation with a carrier equivalence and an identification with the equality graph of that
equivalence. Projecting `.rel` from the package recovers the relation used for terms.

This extra data is valuable: it lets equivalences behave like equality. It also means that a raw
relation between non-equivalent carriers cannot be upgraded to a univalent relation package.
-/

/-- Assuming univalence, universe relation packages are equivalent to carrier equivalences. -/
example (univalent : IsUnivalentUniverse.{u}) (A B : Type u) :
    UnivalentRelation A B ≃ (A ≃ B) :=
  univalentRelationEquivTypeEquivalence univalent A B

/-- Raw parametricity accepts a total relation between `Bool` and `Unit`. -/
def rawBoolUnitRelation : RawUniverseRelation Bool Unit :=
  fun _ _ => Unit

/-- The two-element type `Bool` is not equivalent to the one-element type `Unit`. -/
theorem boolNotEquivalentUnit (equivalence : Bool ≃ Unit) : False := by
  have imagesEqual : equivalence false = equivalence true :=
    Subsingleton.elim _ _
  have falseEqualTrue : false = true := by
    calc
      false = equivalence.symm (equivalence false) := (equivalence.left_inv false).symm
      _ = equivalence.symm (equivalence true) := congrArg equivalence.symm imagesEqual
      _ = true := equivalence.left_inv true
  cases falseEqualTrue

/-- No univalent relation package can relate `Bool` and `Unit`. -/
theorem noUnivalentRelationBoolUnit (package : UnivalentRelation Bool Unit) : False :=
  boolNotEquivalentUnit package.equivalence

end DeepWiki.Refine.ParametricityTranslationTutorial
