import DeepWiki.Refine.RegisteredConstantSyntax

/-! # Typing laws for registered constant translations

Successful constant lookups become sound proof-transfer rules only after the selected source type
has itself been translated and the object language supplies its primed and relational contexts.
-/

namespace DeepWiki.Refine.RegisteredConstantSyntax

/-- Object-language quotation of a translated type witness applied to two endpoints. -/
structure RelationTypeQuotation (Constant : Type u) where
  /-- Quote the relation type represented by `typeWitness` at `left` and `right`. -/
  relationType : {n : Nat} →
    Term Constant n → Term Constant n → Term Constant n → Term Constant n

/-- The primed type and relation witness omitted by a source-only translation context. -/
inductive TranslationContextRealization (Constant : Type u) :
    {n : Nat} → TranslationContext Constant n → Type u where
  /-- The empty translation context needs no omitted binder data. -/
  | empty : TranslationContextRealization Constant TranslationContext.empty
  /-- Realize one source binder by its translated type and its relation witness. -/
  | extend {n : Nat} {context : TranslationContext Constant n}
      {sourceType : Term Constant n}
      (prior : TranslationContextRealization Constant context)
      (primedType : Term Constant n)
      (typeWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n)) :
      TranslationContextRealization Constant (.extend context sourceType)

namespace TranslationContextRealization

/-- Project the context containing every stored primed binder type. -/
def primedContext : {context : TranslationContext Constant n} →
    TranslationContextRealization Constant context → Context Constant n
  | .empty, .empty => .empty
  | .extend _ _, .extend prior primedType _ => .extend prior.primedContext primedType

/-- Build the original/prime/witness context using an explicit relation-type quotation. -/
def relationalContext (quotation : RelationTypeQuotation Constant) :
    {context : TranslationContext Constant n} →
      TranslationContextRealization Constant context →
        Context Constant (AnnotatedRelationTranslation.relationalScope n)
  | .empty, .empty => .empty
  | .extend _ sourceType, .extend prior primedType typeWitness =>
      .extend
        (.extend
          (.extend (prior.relationalContext quotation) sourceType.original)
          (primedType.primed.weakenBy 1))
        (quotation.relationType (typeWitness.weakenBy 2) (.var 1) (.var 0))

/-- A context realization is coherent when each stored binder pair comes from translation. -/
inductive Coherent (environment : Environment Constant)
    (realizers : SyntaxRealizers environment) :
    {context : TranslationContext Constant n} →
      TranslationContextRealization Constant context → Prop where
  /-- The empty realization is coherent. -/
  | empty : Coherent environment realizers TranslationContextRealization.empty
  /-- Extend coherence by a translation of the newly stored source binder type. -/
  | extend {n : Nat} {context : TranslationContext Constant n}
      {sourceType primedType : Term Constant n}
      {typeWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n)}
      {level : Nat} {annotation : Annotation}
      {prior : TranslationContextRealization Constant context}
      (priorCoherent : Coherent environment realizers prior)
      (typeTranslation :
        Judgment environment realizers context sourceType (.sort level annotation)
          primedType typeWitness) :
      Coherent environment realizers
        (TranslationContextRealization.extend (sourceType := sourceType)
          prior primedType typeWitness)

/-- The empty realization projects to the empty primed context. -/
@[simp] theorem primedContext_empty :
    primedContext
        (TranslationContextRealization.empty :
          TranslationContextRealization Constant TranslationContext.empty) =
      Context.empty :=
  rfl

/-- The empty realization projects to the empty relational context. -/
@[simp] theorem relationalContext_empty (quotation : RelationTypeQuotation Constant) :
    relationalContext quotation
        (TranslationContextRealization.empty :
          TranslationContextRealization Constant TranslationContext.empty) =
      Context.empty :=
  rfl

end TranslationContextRealization

/-- Typing obligations for the two outputs of one successful registered translation. -/
def RegisteredTranslationOutputTyping
    (environment : Environment Constant)
    (quotation : RelationTypeQuotation Constant)
    {context : TranslationContext Constant n}
    (realization : TranslationContextRealization Constant context)
    (name : Constant) (primed witness : Term Constant 0)
    (primedType : Term Constant n)
    (typeWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n)) : Prop :=
  HasType environment realization.primedContext
      (primed.weakenClosed n) primedType ∧
    HasType environment (realization.relationalContext quotation)
      (witness.weakenClosed (AnnotatedRelationTranslation.relationalScope n))
      (quotation.relationType typeWitness
        ((.constant name : Term Constant n).original)
        (primed.weakenClosed n).primed)

/-- One lookup is lawful relative to the chosen translation of its source type. -/
def IsLawfulRegisteredTranslation
    (environment : Environment Constant)
    (realizers : SyntaxRealizers environment)
    (quotation : RelationTypeQuotation Constant)
    {context : TranslationContext Constant n}
    (realization : TranslationContextRealization Constant context)
    (name : Constant) (type primed witness : Term Constant 0)
    (primedType : Term Constant n)
    (typeWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n))
    (level : Nat) (annotation : Annotation)
    (_lookup : environment.translation name type = some (primed, witness))
    (_typeTranslation :
      Judgment environment realizers context (type.weakenClosed n)
        (.sort level annotation) primedType typeWitness) : Prop :=
  RegisteredTranslationOutputTyping environment quotation realization name primed witness
    primedType typeWitness

/-- The three typing conclusions required by abstraction for one registered constant branch. -/
def RegisteredConstantAbstractionConclusion
    (environment : Environment Constant)
    (quotation : RelationTypeQuotation Constant)
    {context : TranslationContext Constant n}
    (realization : TranslationContextRealization Constant context)
    (name : Constant) (type primed witness : Term Constant 0)
    (primedType : Term Constant n)
    (typeWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n)) : Prop :=
  HasType environment context.gamma (.constant name) (type.weakenClosed n) ∧
    RegisteredTranslationOutputTyping environment quotation realization name primed witness
      primedType typeWitness

/-- A translation environment validates both registered outputs after translating the source type. -/
structure LawfulTranslationEnvironment
    (environment : Environment Constant)
    (realizers : SyntaxRealizers environment)
    (quotation : RelationTypeQuotation Constant) : Prop
    extends LawfulEnvironment environment where
  /-- Every successful lookup satisfies the primed and witness typing conclusions. -/
  translationLawful :
    ∀ {n : Nat} {context : TranslationContext Constant n}
      {realization : TranslationContextRealization Constant context}
      {name : Constant} {type primed witness : Term Constant 0}
      {primedType : Term Constant n}
      {typeWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n)}
      {level : Nat} {annotation : Annotation},
      TranslationContextRealization.Coherent environment realizers realization →
      WellFormed environment context.gamma →
      (lookup : environment.translation name type = some (primed, witness)) →
      (typeTranslation : Judgment environment realizers context (type.weakenClosed n)
        (.sort level annotation) primedType typeWitness) →
      IsLawfulRegisteredTranslation environment realizers quotation realization name type
        primed witness primedType typeWitness level annotation lookup typeTranslation

/-- A lawful lookup and a translation of its selected source type prove the constant branch. -/
theorem Judgment.constant_abstraction_of_lookup
    {environment : Environment Constant} {realizers : SyntaxRealizers environment}
    {quotation : RelationTypeQuotation Constant}
    (lawful : LawfulTranslationEnvironment environment realizers quotation)
    {context : TranslationContext Constant n}
    {realization : TranslationContextRealization Constant context}
    {name : Constant} {type primed witness : Term Constant 0}
    {primedType : Term Constant n}
    {typeWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n)}
    {level : Nat} {annotation : Annotation}
    (coherent : TranslationContextRealization.Coherent environment realizers realization)
    (contextWellFormed : WellFormed environment context.gamma)
    (lookup : environment.translation name type = some (primed, witness))
    (typeTranslation :
      Judgment environment realizers context (type.weakenClosed n)
        (.sort level annotation) primedType typeWitness) :
    RegisteredConstantAbstractionConclusion environment quotation realization name type
      primed witness primedType typeWitness := by
  constructor
  · exact .constant (Judgment.constant_sourceTyping lookup)
  · exact lawful.translationLawful coherent contextWellFormed lookup typeTranslation

/-- A lawful constant branch synthesizes the lookup outputs and proves all typing conclusions. -/
theorem Judgment.lawful_constant_branch
    {environment : Environment Constant} {realizers : SyntaxRealizers environment}
    {quotation : RelationTypeQuotation Constant}
    (lawful : LawfulTranslationEnvironment environment realizers quotation)
    {context : TranslationContext Constant n}
    {realization : TranslationContextRealization Constant context}
    {name : Constant} {type primed witness : Term Constant 0}
    {primedType : Term Constant n}
    {typeWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n)}
    {level : Nat} {annotation : Annotation}
    (coherent : TranslationContextRealization.Coherent environment realizers realization)
    (contextWellFormed : WellFormed environment context.gamma)
    (lookup : environment.translation name type = some (primed, witness))
    (typeTranslation :
      Judgment environment realizers context (type.weakenClosed n)
        (.sort level annotation) primedType typeWitness) :
    Judgment environment realizers context (.constant name) (type.weakenClosed n)
        (primed.weakenClosed n)
        (witness.weakenClosed (AnnotatedRelationTranslation.relationalScope n)) ∧
      RegisteredConstantAbstractionConclusion environment quotation realization name type
        primed witness primedType typeWitness := by
  exact ⟨.constant lookup,
    constant_abstraction_of_lookup lawful coherent contextWellFormed lookup typeTranslation⟩

/-- Recovering omitted relation witnesses from a source-only translation context. -/
def TranslationContextWitnessRecoveryClaim (Constant : Type u) : Prop :=
  ∃ recover : {n : Nat} → TranslationContext Constant (n + 1) →
      Term Constant (AnnotatedRelationTranslation.relationalScope n),
    ∀ {n : Nat} (context : TranslationContext Constant n)
      (sourceType : Term Constant n)
      (typeWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n)),
      recover (.extend context sourceType) = typeWitness

/-- A source-only translation context cannot determine its omitted relation witnesses. -/
theorem not_translationContextWitnessRecoveryClaim :
    ¬ TranslationContextWitnessRecoveryClaim Constant := by
  rintro ⟨recover, recovers⟩
  let sourceType : Term Constant 0 := .sort 0 Annotation.equivalence
  have first := recovers TranslationContext.empty sourceType
    (.sort 0 Annotation.equivalence :
      Term Constant (AnnotatedRelationTranslation.relationalScope 0))
  have second := recovers TranslationContext.empty sourceType
    (.sort 1 Annotation.equivalence :
      Term Constant (AnnotatedRelationTranslation.relationalScope 0))
  have impossible :
      (.sort 0 Annotation.equivalence :
        Term Constant (AnnotatedRelationTranslation.relationalScope 0)) =
      .sort 1 Annotation.equivalence :=
    first.symm.trans second
  cases impossible

example
    {environment : Environment Constant} {realizers : SyntaxRealizers environment}
    {quotation : RelationTypeQuotation Constant}
    (lawful : LawfulTranslationEnvironment environment realizers quotation)
    {context : TranslationContext Constant n}
    {realization : TranslationContextRealization Constant context}
    {name : Constant} {type primed witness : Term Constant 0}
    {primedType : Term Constant n}
    {typeWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n)}
    {level : Nat} {annotation : Annotation}
    (coherent : TranslationContextRealization.Coherent environment realizers realization)
    (contextWellFormed : WellFormed environment context.gamma)
    (lookup : environment.translation name type = some (primed, witness))
    (typeTranslation :
      Judgment environment realizers context (type.weakenClosed n)
        (.sort level annotation) primedType typeWitness) :
    RegisteredConstantAbstractionConclusion environment quotation realization name type
      primed witness primedType typeWitness :=
  Judgment.constant_abstraction_of_lookup lawful coherent contextWellFormed lookup typeTranslation

end DeepWiki.Refine.RegisteredConstantSyntax
