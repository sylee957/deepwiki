import DeepWiki.Refine.Annotated.Quotation.Syntax

/-! # Contexts for structured-universe quotation

Quotation contexts store extended terms, so a relational binder may use the primitive projected
relation field rather than pretending that this type belongs to the embedded core syntax.
-/

namespace DeepWiki.Refine.StructuredUniverseQuotationContext

open StructuredUniverseQuotationSyntax

/-- A dependent context whose entries are terms of the quotation-extended syntax. -/
inductive Context : Nat → Type where
  /-- The empty quotation context. -/
  | empty : Context 0
  /-- Extend a quotation context by a type in its preceding scope. -/
  | extend {n : Nat} (context : Context n) (type : Term n) : Context (n + 1)
  deriving DecidableEq, Repr

namespace Context

/-- Look up an extended context entry and weaken it into the ambient scope. -/
def lookup : (context : Context n) → Fin n → Term n
  | .empty, index => Fin.elim0 index
  | .extend context type, index =>
      Fin.cases (type.rename DependentCalculus.Renaming.shift)
        (fun older => (context.lookup older).rename DependentCalculus.Renaming.shift) index

/-- The newest quotation-context variable has the weakened extension type. -/
@[simp] theorem lookup_zero (context : Context n) (type : Term n) :
    (Context.extend context type).lookup 0 =
      type.rename DependentCalculus.Renaming.shift :=
  rfl

/-- Looking up an older quotation-context variable weakens its previous type. -/
@[simp] theorem lookup_succ (context : Context n) (type : Term n) (index : Fin n) :
    (Context.extend context type).lookup index.succ =
      (context.lookup index).rename DependentCalculus.Renaming.shift :=
  rfl

/-- Embed an annotated core context into the quotation context syntax. -/
def ofCore : AnnotatedDependentCalculus.Context n → Context n
  | .empty => .empty
  | .extend context type => .extend (ofCore context) (Term.ofCore type)

/-- Lookup commutes with embedding a core context. -/
@[simp] theorem lookup_ofCore (context : AnnotatedDependentCalculus.Context n)
    (index : Fin n) :
    (ofCore context).lookup index = Term.ofCore (context.lookup index) := by
  induction context with
  | empty => exact Fin.elim0 index
  | extend context type inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · simp [ofCore, AnnotatedDependentCalculus.Context.lookup]
      · intro older
        simp [ofCore, AnnotatedDependentCalculus.Context.lookup,
          inductionHypothesis]

end Context

/-- The projected relation type of two fresh endpoints in the genuine quotation syntax. -/
def projectedRelatedDomain (witness : Term n) : Term (n + 2) :=
  relationApplication (.relationProjection (witness.weakenBy 2)) (.var 1) (.var 0)

/-- The annotation argument is computationally irrelevant for the canonical field projector. -/
theorem projectedRelatedDomain_eq_canonical (annotation : Annotation) (witness : Term n) :
    projectedRelatedDomain witness =
      StructuredUniverseQuotationSyntax.RelationFieldQuotation.canonical.relatedDomain
        annotation witness :=
  rfl

/-- Build the source/prime/witness context stored by one explicit context realization. -/
def relationalContext : {n : Nat} →
    {sourceContext : AnnotatedRelationTranslation.Context n} →
    AnnotatedRelationTranslation.ContextRealization sourceContext →
      Context (AnnotatedRelationTranslation.relationalScope n)
  | _, .empty, .empty => .empty
  | _, .extend _ sourceType,
      .extend prior primedType typeWitness =>
    .extend
      (.extend
        (.extend (relationalContext prior)
          (Term.ofCore sourceType.original))
        (Term.ofCore (primedType.primed.weakenBy 1)))
      (projectedRelatedDomain (Term.ofCore typeWitness))

/-- The empty realization gives the empty quotation context. -/
@[simp] theorem relationalContext_empty :
    relationalContext
        (AnnotatedRelationTranslation.ContextRealization.empty :
          AnnotatedRelationTranslation.ContextRealization
            AnnotatedRelationTranslation.Context.empty) =
      Context.empty :=
  rfl

/-- Realizing an extension stores source, prime, and projected-relation binders in order. -/
@[simp] theorem relationalContext_extend
    {sourceContext : AnnotatedRelationTranslation.Context n}
    {sourceType : AnnotatedRelationTranslation.Term n}
    (prior : AnnotatedRelationTranslation.ContextRealization sourceContext)
    (primedType : AnnotatedRelationTranslation.Term n)
    (typeWitness : AnnotatedRelationTranslation.Term
      (AnnotatedRelationTranslation.relationalScope n)) :
    relationalContext
        (AnnotatedRelationTranslation.ContextRealization.extend
          (sourceType := sourceType) prior primedType typeWitness) =
      .extend
        (.extend
          (.extend (relationalContext prior)
            (Term.ofCore sourceType.original))
          (Term.ofCore (primedType.primed.weakenBy 1)))
        (projectedRelatedDomain (Term.ofCore typeWitness)) :=
  rfl

/-- The newest realized entry is the weakened projected relation between the two endpoint binders. -/
theorem relationalContext_extend_lookup_zero
    {sourceContext : AnnotatedRelationTranslation.Context n}
    {sourceType : AnnotatedRelationTranslation.Term n}
    (prior : AnnotatedRelationTranslation.ContextRealization sourceContext)
    (primedType : AnnotatedRelationTranslation.Term n)
    (typeWitness : AnnotatedRelationTranslation.Term
      (AnnotatedRelationTranslation.relationalScope n)) :
    (relationalContext
      (AnnotatedRelationTranslation.ContextRealization.extend
        (sourceType := sourceType) prior primedType typeWitness)).lookup
          ⟨0, by
            simp [AnnotatedRelationTranslation.relationalScope,
              DependentCalculus.RawParametricity.scopeSize_eq]⟩ =
      (projectedRelatedDomain (Term.ofCore typeWitness)).rename
        DependentCalculus.Renaming.shift :=
  rfl

end DeepWiki.Refine.StructuredUniverseQuotationContext
