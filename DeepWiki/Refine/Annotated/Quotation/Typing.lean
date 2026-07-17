import DeepWiki.Refine.Annotated.Quotation.Context

/-! # Typing for structured-universe quotation contexts

A conservative typing fragment validates quotation contexts, variables, and projected-relation
binders. Relation-fiber typehood deliberately forgets its universe level; this module does not
claim the complete annotated typing or abstraction theorem.
-/

namespace DeepWiki.Refine.StructuredUniverseQuotationTyping

open StructuredUniverseQuotationSyntax
open StructuredUniverseQuotationContext

/-- Contexts whose entries use the structured-universe quotation syntax. -/
abbrev Context := StructuredUniverseQuotationContext.Context

mutual

  /-- A quotation context is well formed when every stored entry is an extended-syntax type. -/
  inductive WellFormed : Context n → Prop where
    /-- The empty quotation context is well formed. -/
    | empty : WellFormed .empty
    /-- Extend a well-formed quotation context by a well-formed type. -/
    | extend {context : Context n} {type : Term n}
        (contextWellFormed : WellFormed context)
        (typeWellFormed : IsType context type) :
        WellFormed (.extend context type)

  /-- Typing for the core fragment and structured-relation primitives in quotation contexts. -/
  inductive HasType : Context n → Term n → Term n → Prop where
    /-- A core derivation embeds into the corresponding embedded quotation context. -/
    | core {context : AnnotatedDependentCalculus.Context n}
        {term type : AnnotatedDependentCalculus.Term n}
        (contextWellFormed : AnnotatedDependentCalculus.WellFormed context)
        (typing : AnnotatedDependentCalculus.HasType context term type) :
        HasType (StructuredUniverseQuotationContext.Context.ofCore context)
          (Term.ofCore term) (Term.ofCore type)
    /-- An admissible universe dependency types a quoted sort by its successor sort. -/
    | sort {context : Context n} (contextWellFormed : WellFormed context)
        {source target : Annotation}
        (admissible : AdmissibleUniverseTranslation source target) (level : Nat) :
        HasType context (.sort level source) (.sort (level + 1) target)
    /-- A variable has the weakened type returned by quotation-context lookup. -/
    | var {context : Context n} (contextWellFormed : WellFormed context)
        (index : Fin n) :
        HasType context (.var index) (context.lookup index)
    /-- Extended dependent application instantiates the displayed codomain. -/
    | app {context : Context n} {function argument domain : Term n}
        {codomain : Term (n + 1)}
        (functionTyping : HasType context function (.pi domain codomain))
        (argumentTyping : HasType context argument domain) :
        HasType context (.app function argument) (codomain.instantiate argument)
    /-- A quoted relation family has its displayed binary-relation type. -/
    | relationFamily {context : Context n} (contextWellFormed : WellFormed context)
        (source : Annotation) (level : Nat) :
        HasType context (.relationFamily source level) (relationFamilyType source level)
    /-- An admissible annotation pair supplies its quoted structured universe witness. -/
    | universeWitness {context : Context n} (contextWellFormed : WellFormed context)
        {source target : Annotation}
        (admissible : AdmissibleUniverseTranslation source target) (level : Nat) :
        HasType context (.universeWitness source target level)
          (universeWitnessType source target level)
    /-- Projecting a typed structured witness produces a binary relation on its endpoints. -/
    | relationProjection {context : Context n} {witness left right : Term n}
        {target : Annotation} {level : Nat}
        (witnessTyping : HasType context witness
          (structuredRelationType target level left right)) :
        HasType context (.relationProjection witness) (.relationType left right)
    /-- Typing weakens across one well-formed quotation-context extension. -/
    | weaken {context : Context n} {term type extension : Term n}
        (contextWellFormed : WellFormed context)
        (extensionWellFormed : IsType context extension)
        (typing : HasType context term type) :
        HasType (.extend context extension)
          (term.rename DependentCalculus.Renaming.shift)
          (type.rename DependentCalculus.Renaming.shift)

  /-- Universe-level-erased typehood for entries of a quotation context. -/
  inductive IsType : Context n → Term n → Prop where
    /-- Any term assigned an annotated universe is a context-entry type. -/
    | ofHasType {context : Context n} {type : Term n} {level : Nat}
        {annotation : Annotation}
        (contextWellFormed : WellFormed context)
        (typing : HasType context type (.sort level annotation)) :
        IsType context type
    /-- Applying a typed binary relation to typed endpoints forms a context-entry type. -/
    | relationApplication {context : Context n}
        {relation left right leftType rightType : Term n}
        (contextWellFormed : WellFormed context)
        (relationTyping : HasType context relation (.relationType leftType rightType))
        (leftTyping : HasType context left leftType)
        (rightTyping : HasType context right rightType) :
        IsType context
          (StructuredUniverseQuotationSyntax.relationApplication relation left right)
    /-- Context-entry typehood weakens across one well-formed extension. -/
    | weaken {context : Context n} {type extension : Term n}
        (contextWellFormed : WellFormed context)
        (extensionWellFormed : IsType context extension)
        (typeWellFormed : IsType context type) :
        IsType (.extend context extension)
          (type.rename DependentCalculus.Renaming.shift)

end

/-- Extend a context by two endpoint variables with types from the original scope. -/
def endpointContext (context : Context n) (leftType rightType : Term n) : Context (n + 2) :=
  .extend (.extend context leftType)
    (rightType.rename DependentCalculus.Renaming.shift)

/-- The newest endpoint has the twice-weakened right-endpoint type. -/
@[simp] theorem endpointContext_lookup_zero
    (context : Context n) (leftType rightType : Term n) :
    (endpointContext context leftType rightType).lookup
        (0 : Fin (n + 2)) = rightType.weakenBy 2 :=
  rfl

/-- The preceding endpoint has the twice-weakened left-endpoint type. -/
@[simp] theorem endpointContext_lookup_one
    (context : Context n) (leftType rightType : Term n) :
    (endpointContext context leftType rightType).lookup
        (1 : Fin (n + 2)) = leftType.weakenBy 2 :=
  rfl

/-- Two well-formed endpoint types extend a well-formed quotation context. -/
theorem endpointContext_wellFormed {context : Context n} {leftType rightType : Term n}
    (contextWellFormed : WellFormed context)
    (leftTypeWellFormed : IsType context leftType)
    (rightTypeWellFormed : IsType context rightType) :
    WellFormed (endpointContext context leftType rightType) := by
  exact .extend (.extend contextWellFormed leftTypeWellFormed)
    (.weaken contextWellFormed leftTypeWellFormed rightTypeWellFormed)

namespace HasType

/-- A typing derivation weakens across the two canonical endpoint binders. -/
theorem weakenEndpointContext {context : Context n} {term type leftType rightType : Term n}
    (contextWellFormed : WellFormed context)
    (leftTypeWellFormed : IsType context leftType)
    (rightTypeWellFormed : IsType context rightType)
    (typing : HasType context term type) :
    HasType (endpointContext context leftType rightType)
      (term.weakenBy 2) (type.weakenBy 2) := by
  have firstTyping :=
    HasType.weaken contextWellFormed leftTypeWellFormed typing
  have firstContextWellFormed : WellFormed (.extend context leftType) :=
    .extend contextWellFormed leftTypeWellFormed
  have weakenedRightType :
      IsType (.extend context leftType)
        (rightType.rename DependentCalculus.Renaming.shift) :=
    .weaken contextWellFormed leftTypeWellFormed rightTypeWellFormed
  exact HasType.weaken firstContextWellFormed weakenedRightType firstTyping

end HasType

/-- A twice-weakened structured witness retains its relation-family application type. -/
theorem structuredWitness_weakenEndpointContext
    {context : Context n} {witness leftType rightType : Term n}
    {target : Annotation} {level : Nat}
    (contextWellFormed : WellFormed context)
    (leftTypeWellFormed : IsType context leftType)
    (rightTypeWellFormed : IsType context rightType)
    (witnessTyping : HasType context witness
      (structuredRelationType target level leftType rightType)) :
    HasType (endpointContext context leftType rightType)
      (witness.weakenBy 2)
      (structuredRelationType target level (leftType.weakenBy 2) (rightType.weakenBy 2)) := by
  simpa only [structuredRelationType, Term.weakenBy, Term.rename] using
    HasType.weakenEndpointContext contextWellFormed leftTypeWellFormed
      rightTypeWellFormed witnessTyping

/-- The projected relation of a typed witness forms a type over its two endpoint variables. -/
theorem projectedRelatedDomain_isType
    {context : Context n} {witness leftType rightType : Term n}
    {target : Annotation} {level : Nat}
    (contextWellFormed : WellFormed context)
    (leftTypeWellFormed : IsType context leftType)
    (rightTypeWellFormed : IsType context rightType)
    (witnessTyping : HasType context witness
      (structuredRelationType target level leftType rightType)) :
    IsType (endpointContext context leftType rightType)
      (projectedRelatedDomain witness) := by
  have endpointContextWellFormed := endpointContext_wellFormed contextWellFormed
    leftTypeWellFormed rightTypeWellFormed
  have weakenedWitnessTyping := structuredWitness_weakenEndpointContext
    contextWellFormed leftTypeWellFormed rightTypeWellFormed witnessTyping
  have projectionTyping :
      HasType (endpointContext context leftType rightType)
        (.relationProjection (witness.weakenBy 2))
        (.relationType (leftType.weakenBy 2) (rightType.weakenBy 2)) :=
    .relationProjection weakenedWitnessTyping
  have leftTyping :
      HasType (endpointContext context leftType rightType) (.var 1)
        (leftType.weakenBy 2) := by
    simpa only [endpointContext_lookup_one] using
      HasType.var endpointContextWellFormed (1 : Fin (n + 2))
  have rightTyping :
      HasType (endpointContext context leftType rightType) (.var 0)
        (rightType.weakenBy 2) := by
    simpa only [endpointContext_lookup_zero] using
      HasType.var endpointContextWellFormed (0 : Fin (n + 2))
  exact .relationApplication endpointContextWellFormed projectionTyping leftTyping rightTyping

/-- Extend an endpoint context by its canonical projected-relation binder. -/
def projectedBinderContext (context : Context n) (leftType rightType witness : Term n) :
    Context (n + 3) :=
  .extend (endpointContext context leftType rightType) (projectedRelatedDomain witness)

/-- One realized source-context extension is exactly its projected-binder context extension. -/
theorem relationalContext_extend_eq_projectedBinderContext
    {sourceContext : AnnotatedRelationTranslation.Context n}
    {sourceType : AnnotatedRelationTranslation.Term n}
    (prior : AnnotatedRelationTranslation.ContextRealization sourceContext)
    (primedType : AnnotatedRelationTranslation.Term n)
    (typeWitness : AnnotatedRelationTranslation.Term
      (AnnotatedRelationTranslation.relationalScope n)) :
    StructuredUniverseQuotationContext.relationalContext
        (AnnotatedRelationTranslation.ContextRealization.extend
          (sourceType := sourceType) prior primedType typeWitness) =
      projectedBinderContext
        (StructuredUniverseQuotationContext.relationalContext prior)
        (Term.ofCore sourceType.original)
        (Term.ofCore primedType.primed)
        (Term.ofCore typeWitness) := by
  simp only [StructuredUniverseQuotationContext.relationalContext_extend,
    projectedBinderContext, endpointContext,
    AnnotatedRelationTranslation.Term.weakenBy, Term.ofCore_rename]

/-- A typed structured witness makes its projected-relation binder context well formed. -/
theorem projectedBinderContext_wellFormed
    {context : Context n} {witness leftType rightType : Term n}
    {target : Annotation} {level : Nat}
    (contextWellFormed : WellFormed context)
    (leftTypeWellFormed : IsType context leftType)
    (rightTypeWellFormed : IsType context rightType)
    (witnessTyping : HasType context witness
      (structuredRelationType target level leftType rightType)) :
    WellFormed (projectedBinderContext context leftType rightType witness) :=
  .extend
    (endpointContext_wellFormed contextWellFormed leftTypeWellFormed rightTypeWellFormed)
    (projectedRelatedDomain_isType contextWellFormed leftTypeWellFormed
      rightTypeWellFormed witnessTyping)

/-- The projected-relation variable has the context lookup type of the stored binder. -/
theorem projectedBinderVariable_hasType
    {context : Context n} {witness leftType rightType : Term n}
    {target : Annotation} {level : Nat}
    (contextWellFormed : WellFormed context)
    (leftTypeWellFormed : IsType context leftType)
    (rightTypeWellFormed : IsType context rightType)
    (witnessTyping : HasType context witness
      (structuredRelationType target level leftType rightType)) :
    HasType (projectedBinderContext context leftType rightType witness)
      (.var 0)
      ((projectedRelatedDomain witness).rename DependentCalculus.Renaming.shift) :=
  .var
    (projectedBinderContext_wellFormed contextWellFormed leftTypeWellFormed
      rightTypeWellFormed witnessTyping)
    (0 : Fin (n + 3))

/-- The canonical universe witness yields a well-formed source/prime/relation-binder context. -/
theorem canonicalUniverseProjectedBinderContext_wellFormed
    {source target : Annotation} {level : Nat}
    (admissible : AdmissibleUniverseTranslation source target) :
    WellFormed
      (projectedBinderContext .empty (.sort level source) (.sort level source)
        (.universeWitness source target level)) := by
  have emptyWellFormed : WellFormed
      (StructuredUniverseQuotationContext.Context.empty : Context 0) := .empty
  have sortTyping :
      HasType (StructuredUniverseQuotationContext.Context.empty : Context 0)
        (.sort level source)
        (.sort (level + 1) target) :=
    .sort emptyWellFormed admissible level
  have sortIsType :
      IsType (StructuredUniverseQuotationContext.Context.empty : Context 0)
        (.sort level source) :=
    .ofHasType emptyWellFormed sortTyping
  have witnessTyping :
      HasType (StructuredUniverseQuotationContext.Context.empty : Context 0)
        (.universeWitness source target level)
        (structuredRelationType target level (.sort level source) (.sort level source)) := by
    simpa only [universeWitnessType] using
      HasType.universeWitness emptyWellFormed admissible level
  exact projectedBinderContext_wellFormed emptyWellFormed sortIsType sortIsType witnessTyping

/-- The canonical projected-relation binder is available through typed variable lookup. -/
theorem canonicalUniverseProjectedBinderVariable_hasType
    {source target : Annotation} {level : Nat}
    (admissible : AdmissibleUniverseTranslation source target) :
    HasType
      (projectedBinderContext .empty (.sort level source) (.sort level source)
        (.universeWitness source target level))
      (.var 0)
      ((projectedRelatedDomain
        (.universeWitness source target level : Term 0)).rename
          DependentCalculus.Renaming.shift) := by
  have emptyWellFormed : WellFormed
      (StructuredUniverseQuotationContext.Context.empty : Context 0) := .empty
  have sortTyping :
      HasType (StructuredUniverseQuotationContext.Context.empty : Context 0)
        (.sort level source)
        (.sort (level + 1) target) :=
    .sort emptyWellFormed admissible level
  have sortIsType :
      IsType (StructuredUniverseQuotationContext.Context.empty : Context 0)
        (.sort level source) :=
    .ofHasType emptyWellFormed sortTyping
  have witnessTyping :
      HasType (StructuredUniverseQuotationContext.Context.empty : Context 0)
        (.universeWitness source target level)
        (structuredRelationType target level (.sort level source) (.sort level source)) := by
    simpa only [universeWitnessType] using
      HasType.universeWitness emptyWellFormed admissible level
  exact projectedBinderVariable_hasType emptyWellFormed sortIsType sortIsType witnessTyping

example {source target : Annotation} {level : Nat}
    (admissible : AdmissibleUniverseTranslation source target) :
    WellFormed
      (projectedBinderContext .empty (.sort level source) (.sort level source)
        (.universeWitness source target level)) :=
  canonicalUniverseProjectedBinderContext_wellFormed admissible

end DeepWiki.Refine.StructuredUniverseQuotationTyping
