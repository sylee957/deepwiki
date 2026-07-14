import DeepWiki.Refine.AnnotatedRelationTranslation
import DeepWiki.Refine.RegisteredConstants

/-! # Integrating registered constants into an annotated calculus

An abstract scoped syntax extension embeds the existing annotated typing and translation judgments,
adds genuine global-constant terms, and realizes registry outputs as arbitrary object terms.
-/

namespace DeepWiki.Refine.RegisteredConstants

open AnnotatedDependentCalculus

universe x y z

/-- Weaken a closed annotated type into an arbitrary local scope. -/
def weakenClosedType (type : ClosedAnnotatedType) (scope : Nat) : Term scope :=
  type.rename Fin.elim0

/-- A scoped syntax and judgment extension integrating a fixed global constant registry. -/
structure RegisteredConstantCalculus
    (registry : Registry Constant Output)
    (realizers : AnnotatedRelationTranslation.SyntaxRealizers) where
  /-- Terms of the extended intrinsically scoped annotated language. -/
  ScopedTerm : Nat → Type x
  /-- Typing contexts of the extended annotated language. -/
  TypingContext : Nat → Type y
  /-- Proof-transfer contexts of the extended annotated language. -/
  TranslationContext : Nat → Type z
  /-- Embed every term of the constant-free annotated language. -/
  ofCoreTerm : {n : Nat} → AnnotatedDependentCalculus.Term n → ScopedTerm n
  /-- Core-term embedding is injective. -/
  ofCoreTerm_injective : ∀ {n : Nat}, Function.Injective (@ofCoreTerm n)
  /-- Embed every constant-free annotated typing context. -/
  ofTypingContext : {n : Nat} → AnnotatedDependentCalculus.Context n → TypingContext n
  /-- Embed every constant-free proof-transfer context. -/
  ofTranslationContext : {n : Nat} →
    AnnotatedRelationTranslation.Context n → TranslationContext n
  /-- Form a genuine scoped occurrence of a global constant. -/
  constantTerm : {n : Nat} → Constant → ScopedTerm n
  /-- Distinct global constant names form distinct scoped terms. -/
  constantTerm_injective : ∀ {n : Nat}, Function.Injective (@constantTerm n)
  /-- A global constant occurrence is not an embedded constant-free term. -/
  constantTerm_ne_core : ∀ {n : Nat} (constant : Constant)
    (term : AnnotatedDependentCalculus.Term n), constantTerm constant ≠ ofCoreTerm term
  /-- Embed an arbitrary registered output as an object term at any required scope. -/
  outputTerm : {n : Nat} → Output → ScopedTerm n
  /-- The extended annotated typing judgment. -/
  HasType : {n : Nat} → TypingContext n → ScopedTerm n → ScopedTerm n → Prop
  /-- The extended annotated proof-transfer synthesis judgment. -/
  Translates : {n : Nat} → TranslationContext n →
    ScopedTerm n → ScopedTerm n → ScopedTerm n →
      ScopedTerm (AnnotatedRelationTranslation.relationalScope n) → Prop
  /-- Every constant-free annotated typing derivation embeds into the extended calculus. -/
  ofCoreTyping : ∀ {n : Nat} {context : AnnotatedDependentCalculus.Context n}
      {term type : AnnotatedDependentCalculus.Term n},
    AnnotatedDependentCalculus.HasType context term type →
      HasType (ofTypingContext context) (ofCoreTerm term) (ofCoreTerm type)
  /-- Every constant-free annotated translation derivation embeds into the extended calculus. -/
  ofCoreTranslation : ∀ {n : Nat} {context : AnnotatedRelationTranslation.Context n}
      {term type term' : AnnotatedDependentCalculus.Term n}
      {witness : AnnotatedDependentCalculus.Term
        (AnnotatedRelationTranslation.relationalScope n)},
    AnnotatedRelationTranslation.Judgment realizers context term type term' witness →
      Translates (ofTranslationContext context) (ofCoreTerm term) (ofCoreTerm type)
        (ofCoreTerm term') (ofCoreTerm witness)
  /-- Every positively typed registry entry is a typing rule for its scoped constant term. -/
  constantTyping : ∀ {n : Nat} {context : AnnotatedDependentCalculus.Context n}
      {constant : Constant} {type : ClosedAnnotatedType},
    PositiveTyping registry context constant type →
      HasType (ofTypingContext context) (constantTerm constant)
        (ofCoreTerm (weakenClosedType type n))
  /-- Every successful lookup is a translation rule with arbitrary output terms. -/
  constantTranslation : ∀ {n : Nat}
      {context : AnnotatedRelationTranslation.Context n}
      {constant : Constant} {type : ClosedAnnotatedType} {primed witness : Output},
    RegisteredConstantTranslation registry context constant type primed witness →
      Translates (ofTranslationContext context) (constantTerm constant)
        (ofCoreTerm (weakenClosedType type n)) (outputTerm primed) (outputTerm witness)

namespace RegisteredConstantCalculus

/-- A positive registry derivation lifts to typing in every realizing constant calculus. -/
theorem typing_of_positive
    {registry : Registry Constant Output}
    {realizers : AnnotatedRelationTranslation.SyntaxRealizers}
    (calculus : RegisteredConstantCalculus registry realizers)
    {context : AnnotatedDependentCalculus.Context n} {constant : Constant}
    {type : ClosedAnnotatedType}
    (typing : PositiveTyping registry context constant type) :
    calculus.HasType (calculus.ofTypingContext context) (calculus.constantTerm constant)
      (calculus.ofCoreTerm (weakenClosedType type n)) :=
  calculus.constantTyping typing

/-- A successful registry lookup lifts to synthesis in every realizing constant calculus. -/
theorem translation_of_registered
    {registry : Registry Constant Output}
    {realizers : AnnotatedRelationTranslation.SyntaxRealizers}
    (calculus : RegisteredConstantCalculus registry realizers)
    {context : AnnotatedRelationTranslation.Context n} {constant : Constant}
    {type : ClosedAnnotatedType} {primed witness : Output}
    (translation : RegisteredConstantTranslation registry context constant type primed witness) :
    calculus.Translates (calculus.ofTranslationContext context)
      (calculus.constantTerm constant) (calculus.ofCoreTerm (weakenClosedType type n))
      (calculus.outputTerm primed) (calculus.outputTerm witness) :=
  calculus.constantTranslation translation

/-- A direct registry lookup lifts to synthesis without restricting outputs to constant names. -/
theorem translation_of_lookup
    {registry : Registry Constant Output}
    {realizers : AnnotatedRelationTranslation.SyntaxRealizers}
    (calculus : RegisteredConstantCalculus registry realizers)
    {context : AnnotatedRelationTranslation.Context n} {constant : Constant}
    {type : ClosedAnnotatedType} {primed witness : Output}
    (lookup : registry.translation constant type = some (primed, witness)) :
    calculus.Translates (calculus.ofTranslationContext context)
      (calculus.constantTerm constant) (calculus.ofCoreTerm (weakenClosedType type n))
      (calculus.outputTerm primed) (calculus.outputTerm witness) :=
  calculus.translation_of_registered (.registered lookup)

end RegisteredConstantCalculus

example {registry : Registry Constant Output}
    {realizers : AnnotatedRelationTranslation.SyntaxRealizers}
    (calculus : RegisteredConstantCalculus registry realizers)
    {context : AnnotatedDependentCalculus.Context n} {constant : Constant}
    {type : ClosedAnnotatedType}
    (typing : PositiveTyping registry context constant type) :
    calculus.HasType (calculus.ofTypingContext context) (calculus.constantTerm constant)
      (calculus.ofCoreTerm (weakenClosedType type n)) :=
  calculus.typing_of_positive typing

example {registry : Registry Constant Output}
    {realizers : AnnotatedRelationTranslation.SyntaxRealizers}
    (calculus : RegisteredConstantCalculus registry realizers)
    {context : AnnotatedRelationTranslation.Context n} {constant : Constant}
    {type : ClosedAnnotatedType} {primed witness : Output}
    (lookup : registry.translation constant type = some (primed, witness)) :
    calculus.Translates (calculus.ofTranslationContext context)
      (calculus.constantTerm constant) (calculus.ofCoreTerm (weakenClosedType type n))
      (calculus.outputTerm primed) (calculus.outputTerm witness) :=
  calculus.translation_of_lookup lookup

end DeepWiki.Refine.RegisteredConstants
