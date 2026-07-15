import DeepWiki.Refine.ParametricityTranslations
import DeepWiki.Refine.ParametricitySurfaceSyntax
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

universe u

/-! ## What a context is

Read `⟨⟩, A : □[0], x : A` from left to right:

* `⟨⟩` says that nothing has been assumed yet.
* `A : □[0]` introduces a variable `A` whose value is a small type.
* `x : A` introduces a value `x`; its type may refer to the earlier declaration `A`.

Thus a context is the ordered list of declarations available while checking the expression to the
right of `⊢`. It is not itself a relation and is not the earlier tutorial's `Related` record.
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
theorem universeTypingExample : ccω!{ ⟨⟩ ⊢ □[0] : □[1] } :=
  .sort .empty 0

/-- Looking up `A` in its context proves `A : □[0]`. -/
theorem typeVariableTypingExample : ccω!{ ⟨⟩, A : □[0] ⊢ A : □[0] } :=
  .var typeContextWellFormed 0

/-- Looking up the newest declaration proves `x : A`. -/
theorem valueVariableTypingExample :
    ccω!{ ⟨⟩, A : □[0], x : A ⊢ x : A } :=
  .var typeValueContextWellFormed 0

/-- The polymorphic identity's dependent-product type belongs to `□[1]`. -/
theorem polymorphicIdentityTypeTypingExample :
    ccω!{ ⟨⟩ ⊢ Π A : □[0], Π x : A, A : □[1] } := by
  exact .pi (.sort .empty 0)
    (.pi (.var typeContextWellFormed 0) (.var typeValueContextWellFormed 1))

/-- The named term `λ A, λ x, x` has the polymorphic identity type. -/
theorem polymorphicIdentityTypingExample :
    ccω!{ ⟨⟩ ⊢
      λ A : □[0], λ x : A, x :
      Π A : □[0], Π x : A, A } := by
  exact .lam (.sort .empty 0)
    (.lam (.var typeContextWellFormed 0) (.var typeValueContextWellFormed 0))

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

/-- Cumulativity also regards `□[0]` as an element of the still higher universe `□[2]`. -/
theorem universeCumulativityExample : ccω!{ ⟨⟩ ⊢ □[0] : □[2] } :=
  HasType.sort_of_lt .empty (by decide)

/-- The conversion rule accepts a beta-expanded presentation of the type `A`. -/
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

/-! ## Raw context translation

Raw parametricity simultaneously studies three versions of each source expression:

* `t` is the original expression, renamed into the translated context.
* `t′` is a fresh primed copy.
* `⟦t⟧` is evidence that `t` and `t′` are related.

Consequently, one source declaration `x : A` becomes three target declarations:

`x : A, x′ : A′, xᴿ : ⟦A⟧ x x′`.

For `A : □[0], x : A`, the whole translated context is therefore ordered as
`A, A′, Aᴿ, x, x′, xᴿ`. Because the kernel uses newest-first de Bruijn indices, the last three have
indices `xᴿ = 0`, `x′ = 1`, and `x = 2`.
-/

/-- Translating `A : □[0]` produces a context containing the triple `A, A′, Aᴿ`. -/
def translatedTypeContext : Context 3 :=
  rawωctx!{ ⟨⟩, A : □[0] }

/-- The translated one-type context is well formed. -/
theorem translatedTypeContextWellFormed : WellFormed translatedTypeContext :=
  context_extend_wellFormed context_empty_wellFormed
    (.sort .empty 0)
    (translate_sort_witness_hasType context_empty_wellFormed 0)

/-- Translating `A : □[0], x : A` produces six dependent declarations. -/
def translatedTypeValueContext : Context 6 :=
  rawωctx!{ ⟨⟩, A : □[0], x : A }

/-- The translated type-and-value context is well formed. -/
theorem translatedTypeValueContextWellFormed : WellFormed translatedTypeValueContext :=
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
  ccωterm!{ ⟨⟩, A : □[0], x : A ⊢ x }

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
