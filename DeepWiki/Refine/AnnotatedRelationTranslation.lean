import DeepWiki.Refine.AnnotatedDependentCalculus
import DeepWiki.Refine.Parametricity.Raw.Translation
import DeepWiki.Refine.Parametricity.Sequents.Raw

/-! # Scoped annotated proof transfer

An intrinsically scoped synthesis judgment translates annotated dependent terms together with
proof-relevant witnesses. Source and primed terms use parallel scopes; witnesses use the
corresponding three-copy relational scope. Explicit relation-field quotation and context
realizations isolate the remaining structured-witness typing obligation.
-/

namespace DeepWiki.Refine.AnnotatedRelationTranslation

/-- Terms of the annotated dependent object language. -/
abbrev Term := AnnotatedDependentCalculus.Term

/-- Number of original, primed, and witness variables generated from an `n`-variable scope. -/
abbrev relationalScope (n : Nat) := DependentCalculus.RawParametricity.scopeSize n

/-- The source and three-copy relation-witness scopes coincide only for an empty context. -/
theorem relationalScope_eq_sourceScope_iff (n : Nat) :
    relationalScope n = n ↔ n = 0 := by
  simp only [relationalScope, DependentCalculus.RawParametricity.scopeSize_eq]
  omega

namespace Term

/-- Form a non-dependent arrow in the annotated object language. -/
def arrow (domain codomain : Term n) : Term n :=
  AnnotatedDependentCalculus.Term.arrow domain codomain

/-- Rename an annotated term into the original-variable part of its relational scope. -/
def original (term : Term n) : Term (relationalScope n) :=
  term.rename (DependentCalculus.RawParametricity.originalRenaming n)

/-- Rename an annotated term into the primed-variable part of its relational scope. -/
def primed (term : Term n) : Term (relationalScope n) :=
  term.rename (DependentCalculus.RawParametricity.primedRenaming n)

/-- Weaken an annotated term by a specified number of fresh variables. -/
def weakenBy (term : Term n) : (amount : Nat) → Term (n + amount)
  | 0 => term
  | amount + 1 => (weakenBy term amount).rename DependentCalculus.Renaming.shift

/-- Apply a function witness to an original argument, its primed image, and its witness. -/
def applyWitness (functionWitness : Term (relationalScope n))
    (argument argument' : Term n) (argumentWitness : Term (relationalScope n)) :
    Term (relationalScope n) :=
  .app (.app (.app functionWitness argument.original) argument'.primed) argumentWitness

/-- The relation type of a fresh original and primed binder induced by a domain witness. -/
def relatedDomain (domainWitness : Term (relationalScope n)) :
    Term (relationalScope n + 2) :=
  .app (.app (domainWitness.weakenBy 2) (.var 1)) (.var 0)

/-- Abstract a body witness over an original, primed, and relation-witness variable. -/
def lambdaWitness (domain domain' : Term n)
    (domainWitness : Term (relationalScope n))
    (bodyWitness : Term (relationalScope n + 3)) : Term (relationalScope n) :=
  .lam domain.original
    (.lam (domain'.primed.weakenBy 1)
      (.lam domainWitness.relatedDomain bodyWitness))

/-- Erasure commutes with embedding an annotated term in the original relational scope. -/
@[simp] theorem erase_original (term : Term n) :
    term.original.erase = DependentCalculus.RawParametricity.original term.erase := by
  simp [original, DependentCalculus.RawParametricity.original]

/-- Erasure commutes with embedding an annotated term in the primed relational scope. -/
@[simp] theorem erase_primed (term : Term n) :
    term.primed.erase = DependentCalculus.RawParametricity.primed term.erase := by
  simp [primed, DependentCalculus.RawParametricity.primed]

/-- Erasure commutes with weakening by any number of fresh variables. -/
@[simp] theorem erase_weakenBy (term : Term n) (amount : Nat) :
    (term.weakenBy amount).erase =
      DependentCalculus.RawParametricity.weakenBy term.erase amount := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      simp only [weakenBy, DependentCalculus.RawParametricity.weakenBy,
        AnnotatedDependentCalculus.Term.erase_rename, inductionHypothesis]

/-- Erasure sends an annotated related-domain type to its raw counterpart. -/
@[simp] theorem erase_relatedDomain (domainWitness : Term (relationalScope n)) :
    domainWitness.relatedDomain.erase =
      DependentCalculus.ParametricitySequents.relatedDomain domainWitness.erase := by
  simp only [relatedDomain, DependentCalculus.ParametricitySequents.relatedDomain,
    AnnotatedDependentCalculus.Term.erase, erase_weakenBy]

/-- Erasure sends an annotated lambda witness to the raw parametricity lambda witness. -/
@[simp] theorem erase_lambdaWitness (domain domain' : Term n)
    (domainWitness : Term (relationalScope n))
    (bodyWitness : Term (relationalScope n + 3)) :
    (lambdaWitness domain domain' domainWitness bodyWitness).erase =
      DependentCalculus.ParametricitySequents.lambdaWitness
        domain.original.erase domain'.primed.erase domainWitness.relatedDomain.erase
        bodyWitness.erase := by
  simp only [lambdaWitness, DependentCalculus.ParametricitySequents.lambdaWitness,
    AnnotatedDependentCalculus.Term.erase, erase_weakenBy]

end Term

/-- A dependent source context used to synthesize primed terms and relational witnesses. -/
inductive Context : Nat → Type where
  /-- The empty proof-transfer context. -/
  | empty : Context 0
  /-- Extend a proof-transfer context by one annotated source type. -/
  | extend {n : Nat} (context : Context n) (sourceType : Term n) : Context (n + 1)
  deriving DecidableEq, Repr

namespace Context

/-- Erase translation data to the annotated source typing context. -/
def gamma : Context n → AnnotatedDependentCalculus.Context n
  | .empty => .empty
  | .extend context sourceType => .extend context.gamma sourceType

/-- A context entry records an original variable, its type, its primed variable, and its witness. -/
structure Entry (n : Nat) where
  /-- The original variable. -/
  original : Fin n
  /-- The annotated type of the original variable in the ambient source scope. -/
  sourceType : Term n
  /-- The corresponding variable in the parallel primed scope. -/
  primed : Fin n
  /-- The corresponding relation-witness variable in the three-copy scope. -/
  witness : Fin (relationalScope n)
  deriving DecidableEq, Repr

/-- The canonical quadruple associated with a source variable in a proof-transfer context. -/
def entryAt (context : Context n) (index : Fin n) : Entry n where
  original := index
  sourceType := context.gamma.lookup index
  primed := index
  witness := DependentCalculus.RawParametricity.witnessRenaming n index

/-- Enumerate the original/type/prime/witness quadruples of a proof-transfer context. -/
def entries (context : Context n) : List (Entry n) :=
  List.ofFn context.entryAt

/-- A quadruple belongs to a proof-transfer context when it occurs in its canonical enumeration. -/
def Contains (context : Context n) (entry : Entry n) : Prop :=
  entry ∈ context.entries

/-- Membership exposes the unique source index from which a canonical context entry was built. -/
theorem exists_entryAt_of_contains {context : Context n} {entry : Entry n}
    (member : context.Contains entry) :
    ∃ index, context.entryAt index = entry := by
  simpa only [Contains, entries, List.mem_ofFn] using member

/-- Original and primed indices coincide because they inhabit parallel copies of one scope. -/
theorem original_eq_primed_of_contains {context : Context n} {entry : Entry n}
    (member : context.Contains entry) : entry.original = entry.primed := by
  obtain ⟨index, rfl⟩ := exists_entryAt_of_contains member
  rfl

/-- Erasing the empty proof-transfer context gives the empty annotated context. -/
@[simp] theorem gamma_empty :
    gamma Context.empty = AnnotatedDependentCalculus.Context.empty :=
  rfl

/-- Erasure preserves dependent context extension. -/
@[simp] theorem gamma_extend (context : Context n) (sourceType : Term n) :
    gamma (.extend context sourceType) = .extend context.gamma sourceType :=
  rfl

/-- A canonical entry carries the lookup type of its original variable. -/
@[simp] theorem entryAt_sourceType (context : Context n) (index : Fin n) :
    (context.entryAt index).sourceType = context.gamma.lookup index :=
  rfl

end Context

/-- An object-language realization of the annotation-indexed universe relation constructor. -/
abbrev UniverseWitness (n : Nat) := Term (relationalScope n)

/-- An object-language realization of an annotation-indexed arrow relation constructor. -/
abbrev ArrowWitnessOperator (n : Nat) :=
  Term n → Term n → Term n → Term n →
    Term (relationalScope n) → Term (relationalScope n) → Term (relationalScope n)

/-- An object-language realization of an annotation-indexed dependent-product relation constructor. -/
abbrev PiWitnessOperator (n : Nat) :=
  Term n → Term n → Term (n + 1) → Term (n + 1) →
    Term (relationalScope n) → Term (relationalScope n + 3) → Term (relationalScope n)

/-- An object-language realization of recursive witness weakening along annotated subtyping. -/
abbrev WitnessWeakening (n : Nat) :=
  Term (relationalScope n) → Term (relationalScope n)

/-- Fixed object-language realizers shared by every rule of one annotated translation. -/
structure SyntaxRealizers where
  /-- Realize the universe witness selected by source annotation, target annotation, and level. -/
  universeRule : {n : Nat} → Annotation → Annotation → Nat → UniverseWitness n
  /-- Realize the non-dependent arrow constructor selected by its output annotation. -/
  arrow : {n : Nat} → Annotation → ArrowWitnessOperator n
  /-- Realize the dependent-product constructor selected by its output annotation. -/
  pi : {n : Nat} → Annotation → PiWitnessOperator n
  /-- Realize recursive weakening for a particular annotated subtyping derivation. -/
  weakening : {n : Nat} → (context : Context n) → {source target : Term n} →
    AnnotatedDependentCalculus.Subtype context.gamma source target → WitnessWeakening n

/-- The scoped four-place synthesis judgment generated by fixed syntax realizers. -/
inductive Judgment (realizers : SyntaxRealizers) : (context : Context n) →
    Term n → Term n → Term n → Term (relationalScope n) → Prop where
  /-- Admissible universe annotations synthesize the corresponding universe relation witness. -/
  | sort {context : Context n} {source target : Annotation}
      (admissible : AdmissibleUniverseTranslation source target) (level : Nat) :
      Judgment realizers context (.sort level source) (.sort (level + 1) target)
        (.sort level source) (realizers.universeRule source target level)
  /-- A well-formed context quadruple translates its original variable to its primed and witness variables. -/
  | var {context : Context n} {entry : Context.Entry n}
      (member : context.Contains entry)
      (contextWellFormed : AnnotatedDependentCalculus.WellFormed context.gamma) :
      Judgment realizers context (.var entry.original) entry.sourceType
        (.var entry.primed) (.var entry.witness)
  /-- Application synthesizes by applying the function witness to both arguments and their witness. -/
  | app {context : Context n} {function function' argument argument' domain : Term n}
      {codomain : Term (n + 1)}
      {functionWitness argumentWitness : Term (relationalScope n)}
      (functionTranslation :
        Judgment realizers context function (.pi domain codomain) function' functionWitness)
      (argumentTranslation :
        Judgment realizers context argument domain argument' argumentWitness) :
      Judgment realizers context (.app function argument) (codomain.instantiate argument)
        (.app function' argument')
        (functionWitness.applyWitness argument argument' argumentWitness)
  /-- Lambda synthesis translates its domain and body and abstracts the body witness over three variables. -/
  | lam {context : Context n} {domain domain' : Term n}
      {body codomain body' : Term (n + 1)} {level : Nat} {annotation : Annotation}
      {domainWitness : Term (relationalScope n)}
      {bodyWitness : Term (relationalScope n + 3)}
      (domainTranslation :
        Judgment realizers context domain (.sort level annotation) domain' domainWitness)
      (bodyTranslation :
        Judgment realizers (.extend context domain) body codomain body' bodyWitness) :
      Judgment realizers context (.lam domain body) (.pi domain codomain) (.lam domain' body')
        (Term.lambdaWitness domain domain' domainWitness bodyWitness)
  /-- Non-dependent arrows use the displayed arrow dependency requirements of the output annotation. -/
  | arrow {context : Context n} {domain domain' codomain codomain' : Term n}
      {level : Nat} {domainAnnotation codomainAnnotation outputAnnotation : Annotation}
      {domainWitness codomainWitness : Term (relationalScope n)}
      (requirements :
        (domainAnnotation, codomainAnnotation) = arrowRequirements outputAnnotation)
      (domainTranslation :
        Judgment realizers context domain (.sort level domainAnnotation) domain' domainWitness)
      (codomainTranslation :
        Judgment realizers context codomain (.sort level codomainAnnotation) codomain'
          codomainWitness) :
      Judgment realizers context (Term.arrow domain codomain) (.sort level outputAnnotation)
        (Term.arrow domain' codomain')
        (realizers.arrow outputAnnotation domain domain' codomain codomain'
          domainWitness codomainWitness)
  /-- Dependent products use the displayed product dependency requirements of the output annotation. -/
  | pi {context : Context n} {domain domain' : Term n}
      {codomain codomain' : Term (n + 1)} {level : Nat}
      {domainAnnotation codomainAnnotation outputAnnotation : Annotation}
      {domainWitness : Term (relationalScope n)}
      {codomainWitness : Term (relationalScope n + 3)}
      (requirements :
        (domainAnnotation, codomainAnnotation) =
          dependentProductRequirements outputAnnotation)
      (domainTranslation :
        Judgment realizers context domain (.sort level domainAnnotation) domain' domainWitness)
      (codomainTranslation :
        Judgment realizers (.extend context domain) codomain (.sort level codomainAnnotation)
          codomain' codomainWitness) :
      Judgment realizers context (.pi domain codomain) (.sort level outputAnnotation)
        (.pi domain' codomain')
        (realizers.pi outputAnnotation domain domain' codomain codomain'
          domainWitness codomainWitness)
  /-- Conversion weakens a synthesized witness along annotated subtyping. -/
  | conversion {context : Context n} {term type type' term' : Term n}
      {termWitness : Term (relationalScope n)}
      (translation : Judgment realizers context term type term' termWitness)
      (subtype : AnnotatedDependentCalculus.Subtype context.gamma type type') :
      Judgment realizers context term type' term'
        (realizers.weakening context subtype termWitness)

/-- The scoped representation uses identical syntax for the source and parallel primed copies. -/
theorem Judgment.primed_eq_source {realizers : SyntaxRealizers}
    {context : Context n} {term type term' : Term n}
    {termWitness : Term (relationalScope n)}
    (translation : Judgment realizers context term type term' termWitness) :
    term' = term := by
  induction translation with
  | sort => rfl
  | var member contextWellFormed =>
      rw [Context.original_eq_primed_of_contains member]
  | app functionTranslation argumentTranslation functionInduction argumentInduction =>
      simp only [functionInduction, argumentInduction]
  | lam domainTranslation bodyTranslation domainInduction bodyInduction =>
      simp only [domainInduction, bodyInduction]
  | arrow requirements domainTranslation codomainTranslation
      domainInduction codomainInduction =>
      simp only [domainInduction, codomainInduction]
  | pi requirements domainTranslation codomainTranslation
      domainInduction codomainInduction =>
      simp only [domainInduction, codomainInduction]
  | conversion translation subtype inductionHypothesis =>
      exact inductionHypothesis

/-- Object-language quotation data for expressing witness typing in the relational scope. -/
structure WitnessTypingBridge where
  /-- The annotated typing context for the original/prime/witness expansion of a source context. -/
  relationalContext : {n : Nat} →
    Context n → AnnotatedDependentCalculus.Context (relationalScope n)
  /-- Quote application of a relation record to an original and a primed term. -/
  relationType : {n : Nat} →
    Term n → Term n → Term n → Term n

/-- Object-language syntax for projecting and applying the relation field of a structured witness. -/
structure RelationFieldQuotation where
  /-- Quote the relation field of an annotation-indexed structured witness. -/
  relationField : {n : Nat} → Annotation → Term n → Term n

namespace RelationFieldQuotation

/-- Apply a quoted relation field to a left and a right endpoint. -/
def application (quotation : RelationFieldQuotation) (annotation : Annotation)
    (witness left right : Term n) : Term n :=
  .app (.app (quotation.relationField annotation witness) left) right

/-- Form the quoted relation type of the two newest endpoint variables. -/
def relatedDomain (quotation : RelationFieldQuotation) (annotation : Annotation)
    (witness : Term n) : Term (n + 2) :=
  quotation.application annotation (witness.weakenBy 2) (.var 1) (.var 0)

/-- Abstract a body witness using an explicit structured-relation projection at its third binder. -/
def lambdaWitness (quotation : RelationFieldQuotation) (annotation : Annotation)
    (domain domain' : Term n) (domainWitness : Term n)
    (bodyWitness : Term (n + 3)) : Term n :=
  .lam domain
    (.lam (domain'.weakenBy 1)
      (.lam (quotation.relatedDomain annotation domainWitness) bodyWitness))

end RelationFieldQuotation

/-- A bridge is quotation-backed when its relation type is explicit relation-field application. -/
structure QuotationBackedBridge (bridge : WitnessTypingBridge)
    (quotation : RelationFieldQuotation) : Prop where
  /-- The bridge exposes the quoted relation field at every annotation and scope. -/
  relationType_eq : ∀ {n : Nat} (annotation : Annotation)
      (witness left right : Term n),
    bridge.relationType witness left right =
      quotation.application annotation witness left right

/-- A context realization stores the primed type and structured witness omitted by `Context`. -/
inductive ContextRealization : {n : Nat} → (context : Context n) → Type where
  /-- The empty source context has an empty realization. -/
  | empty : ContextRealization Context.empty
  /-- Realize one source extension by its primed type and structured relation witness. -/
  | extend {n : Nat} {context : Context n} {sourceType : Term n}
      (prior : ContextRealization context) (primedType : Term n)
      (typeWitness : Term (relationalScope n)) :
      ContextRealization (.extend context sourceType)

namespace ContextRealization

/-- Project the context containing the stored primed types. -/
def primedContext : {context : Context n} →
    ContextRealization context → AnnotatedDependentCalculus.Context n
  | .empty, .empty => .empty
  | .extend _ _, .extend prior primedType _ =>
      .extend prior.primedContext primedType

/-- Build the three-copy typing context using the bridge's quoted relation application. -/
def relationalContext (bridge : WitnessTypingBridge) : {context : Context n} →
    ContextRealization context →
      AnnotatedDependentCalculus.Context (relationalScope n)
  | .empty, .empty => .empty
  | .extend _ sourceType, .extend prior primedType typeWitness =>
      .extend
        (.extend
          (.extend (prior.relationalContext bridge) sourceType.original)
          (primedType.primed.weakenBy 1))
        (bridge.relationType (typeWitness.weakenBy 2) (.var 1) (.var 0))

/-- A realization is coherent when every stored binder pair is produced by translation. -/
inductive Coherent (realizers : SyntaxRealizers) :
    {context : Context n} → ContextRealization context → Prop where
  /-- The empty realization is coherent. -/
  | empty : Coherent realizers ContextRealization.empty
  /-- Extend coherence with a translation of the source binder type. -/
  | extend {n : Nat} {context : Context n} {sourceType primedType : Term n}
      {typeWitness : Term (relationalScope n)} {level : Nat} {annotation : Annotation}
      {prior : ContextRealization context}
      (priorCoherent : Coherent realizers prior)
      (typeTranslation :
        Judgment realizers context sourceType (.sort level annotation)
          primedType typeWitness) :
      Coherent realizers
        (ContextRealization.extend (sourceType := sourceType) prior primedType typeWitness)

/-- A coherent realization's primed context is the parallel copy of its source context. -/
theorem Coherent.primedContext_eq_gamma {realizers : SyntaxRealizers}
    {context : Context n} {realization : ContextRealization context}
    (coherent : Coherent realizers realization) :
    realization.primedContext = context.gamma := by
  induction coherent with
  | empty => rfl
  | extend priorCoherent typeTranslation inductionHypothesis =>
      simp only [primedContext, Context.gamma_extend, inductionHypothesis,
        typeTranslation.primed_eq_source]

/-- The empty realization projects to the empty primed context. -/
@[simp] theorem primedContext_empty :
    primedContext (ContextRealization.empty : ContextRealization Context.empty) =
      AnnotatedDependentCalculus.Context.empty :=
  rfl

/-- The empty realization projects to the empty relational context. -/
@[simp] theorem relationalContext_empty (bridge : WitnessTypingBridge) :
    relationalContext bridge
        (ContextRealization.empty : ContextRealization Context.empty) =
      AnnotatedDependentCalculus.Context.empty :=
  rfl

end ContextRealization

/-- Recovering arbitrary omitted binder witnesses from `Context` alone is impossible. -/
def ContextWitnessRecoveryClaim : Prop :=
  ∃ recover : {n : Nat} → Context (n + 1) → Term (relationalScope n),
    ∀ {n : Nat} (context : Context n) (sourceType : Term n)
      (typeWitness : Term (relationalScope n)),
      recover (.extend context sourceType) = typeWitness

/-- The source-only context cannot determine the omitted structured witness of an extension. -/
theorem not_contextWitnessRecoveryClaim : ¬ ContextWitnessRecoveryClaim := by
  rintro ⟨recover, recovers⟩
  let sourceType : Term 0 := .sort 0 Annotation.equivalence
  have first := recovers Context.empty sourceType
    (.sort 0 Annotation.equivalence : Term (relationalScope 0))
  have second := recovers Context.empty sourceType
    (.sort 1 Annotation.equivalence : Term (relationalScope 0))
  have impossible :
      ((.sort 0 Annotation.equivalence : Term (relationalScope 0))) =
        .sort 1 Annotation.equivalence := first.symm.trans second
  cases impossible

/-- The abstraction conclusion types the primed term and the synthesized relational witness. -/
def AbstractionConclusion (bridge : WitnessTypingBridge) (context : Context n)
    (term term' type' : Term n)
    (termWitness typeWitness : Term (relationalScope n)) : Prop :=
  AnnotatedDependentCalculus.HasType context.gamma term' type' ∧
    AnnotatedDependentCalculus.HasType (bridge.relationalContext context) termWitness
      (bridge.relationType typeWitness term.original term'.primed)

/-- The witness-only part of the abstraction theorem after parallel-copy typing is discharged. -/
def WitnessTypingConclusion (bridge : WitnessTypingBridge) (context : Context n)
    (term term' : Term n) (termWitness typeWitness : Term (relationalScope n)) : Prop :=
  AnnotatedDependentCalculus.HasType (bridge.relationalContext context) termWitness
    (bridge.relationType typeWitness term.original term'.primed)

/-- The abstraction claim for a fixed-realizer synthesis derivation and translation of its type. -/
def AbstractionClaim (realizers : SyntaxRealizers) (bridge : WitnessTypingBridge) : Prop :=
  ∀ {n : Nat} {context : Context n}
    {term termType term' type' : Term n}
    {termWitness typeWitness : Term (relationalScope n)}
    {level : Nat} {annotation : Annotation},
    AnnotatedDependentCalculus.WellFormed context.gamma →
    AnnotatedDependentCalculus.HasType context.gamma term termType →
    Judgment realizers context term termType term' termWitness →
    Judgment realizers context termType (.sort level annotation) type' typeWitness →
    AbstractionConclusion bridge context term term' type'
      termWitness typeWitness

/-- The exact remaining witness-typing obligation of the scoped abstraction theorem. -/
def WitnessAbstractionClaim (realizers : SyntaxRealizers)
    (bridge : WitnessTypingBridge) : Prop :=
  ∀ {n : Nat} {context : Context n}
    {term termType term' type' : Term n}
    {termWitness typeWitness : Term (relationalScope n)}
    {level : Nat} {annotation : Annotation},
    AnnotatedDependentCalculus.WellFormed context.gamma →
    AnnotatedDependentCalculus.HasType context.gamma term termType →
    Judgment realizers context term termType term' termWitness →
    Judgment realizers context termType (.sort level annotation) type' typeWitness →
    WitnessTypingConclusion bridge context term term' termWitness typeWitness

/-- Parallel-copy typing is automatic, so abstraction is equivalent to witness typing alone. -/
theorem abstractionClaim_iff_witnessAbstractionClaim
    (realizers : SyntaxRealizers) (bridge : WitnessTypingBridge) :
    AbstractionClaim realizers bridge ↔ WitnessAbstractionClaim realizers bridge := by
  constructor
  · intro abstraction n context term termType term' type' termWitness typeWitness
      level annotation contextWellFormed termWellTyped termTranslation typeTranslation
    exact (abstraction contextWellFormed termWellTyped termTranslation typeTranslation).2
  · intro witnessAbstraction n context term termType term' type' termWitness typeWitness
      level annotation contextWellFormed termWellTyped termTranslation typeTranslation
    constructor
    · simpa only [termTranslation.primed_eq_source, typeTranslation.primed_eq_source] using
        termWellTyped
    · exact witnessAbstraction contextWellFormed termWellTyped termTranslation typeTranslation

/-- The faithful context-indexed conclusion uses stored primed and witness binder types. -/
def RealizedAbstractionConclusion (bridge : WitnessTypingBridge)
    {context : Context n} (realization : ContextRealization context)
    (term term' type' : Term n)
    (termWitness typeWitness : Term (relationalScope n)) : Prop :=
  AnnotatedDependentCalculus.HasType realization.primedContext term' type' ∧
    AnnotatedDependentCalculus.HasType (realization.relationalContext bridge) termWitness
      (bridge.relationType typeWitness term.original term'.primed)

/-- The remaining witness judgment in a context realization carrying every binder translation. -/
def RealizedWitnessTypingConclusion (bridge : WitnessTypingBridge)
    {context : Context n} (realization : ContextRealization context)
    (term term' : Term n) (termWitness typeWitness : Term (relationalScope n)) : Prop :=
  AnnotatedDependentCalculus.HasType (realization.relationalContext bridge) termWitness
    (bridge.relationType typeWitness term.original term'.primed)

/-- A context-faithful abstraction claim makes all omitted binder translations explicit. -/
def RealizedAbstractionClaim (realizers : SyntaxRealizers)
    (bridge : WitnessTypingBridge) : Prop :=
  ∀ {n : Nat} {context : Context n} {realization : ContextRealization context}
    {term termType term' type' : Term n}
    {termWitness typeWitness : Term (relationalScope n)}
    {level : Nat} {annotation : Annotation},
    ContextRealization.Coherent realizers realization →
    AnnotatedDependentCalculus.WellFormed context.gamma →
    AnnotatedDependentCalculus.HasType context.gamma term termType →
    Judgment realizers context term termType term' termWitness →
    Judgment realizers context termType (.sort level annotation) type' typeWitness →
    RealizedAbstractionConclusion bridge realization term term' type'
      termWitness typeWitness

/-- The exact context-faithful witness-typing obligation after primed typing is discharged. -/
def RealizedWitnessAbstractionClaim (realizers : SyntaxRealizers)
    (bridge : WitnessTypingBridge) : Prop :=
  ∀ {n : Nat} {context : Context n} {realization : ContextRealization context}
    {term termType term' type' : Term n}
    {termWitness typeWitness : Term (relationalScope n)}
    {level : Nat} {annotation : Annotation},
    ContextRealization.Coherent realizers realization →
    AnnotatedDependentCalculus.WellFormed context.gamma →
    AnnotatedDependentCalculus.HasType context.gamma term termType →
    Judgment realizers context term termType term' termWitness →
    Judgment realizers context termType (.sort level annotation) type' typeWitness →
    RealizedWitnessTypingConclusion bridge realization term term'
      termWitness typeWitness

/-- Context-faithful abstraction is equivalent to its structured-witness typing component. -/
theorem realizedAbstractionClaim_iff_witnessAbstractionClaim
    (realizers : SyntaxRealizers) (bridge : WitnessTypingBridge) :
    RealizedAbstractionClaim realizers bridge ↔
      RealizedWitnessAbstractionClaim realizers bridge := by
  constructor
  · intro abstraction n context realization term termType term' type' termWitness
      typeWitness level annotation coherent contextWellFormed termWellTyped termTranslation
      typeTranslation
    exact (abstraction coherent contextWellFormed termWellTyped termTranslation typeTranslation).2
  · intro witnessAbstraction n context realization term termType term' type' termWitness
      typeWitness level annotation coherent contextWellFormed termWellTyped termTranslation
      typeTranslation
    constructor
    · rw [coherent.primedContext_eq_gamma]
      simpa only [termTranslation.primed_eq_source, typeTranslation.primed_eq_source] using
        termWellTyped
    · exact witnessAbstraction coherent contextWellFormed termWellTyped termTranslation
        typeTranslation

example {realizers : SyntaxRealizers} {context : Context n} {source target : Annotation}
    (admissible : AdmissibleUniverseTranslation source target) (level : Nat)
    : Judgment realizers context (.sort level source) (.sort (level + 1) target)
      (.sort level source) (realizers.universeRule source target level) :=
  .sort admissible level

example {realizers : SyntaxRealizers} {context : Context n} {entry : Context.Entry n}
    (member : context.Contains entry)
    (contextWellFormed : AnnotatedDependentCalculus.WellFormed context.gamma) :
    Judgment realizers context (.var entry.original) entry.sourceType
      (.var entry.primed) (.var entry.witness) :=
  .var member contextWellFormed

example {realizers : SyntaxRealizers} {context : Context n}
    {function function' argument argument' domain : Term n}
    {codomain : Term (n + 1)}
    {functionWitness argumentWitness : Term (relationalScope n)}
    (functionTranslation :
      Judgment realizers context function (.pi domain codomain) function' functionWitness)
    (argumentTranslation :
      Judgment realizers context argument domain argument' argumentWitness) :
    Judgment realizers context (.app function argument) (codomain.instantiate argument)
      (.app function' argument')
      (functionWitness.applyWitness argument argument' argumentWitness) :=
  .app functionTranslation argumentTranslation

example {realizers : SyntaxRealizers} {context : Context n} {domain domain' : Term n}
    {body codomain body' : Term (n + 1)} {level : Nat} {annotation : Annotation}
    {domainWitness : Term (relationalScope n)}
    {bodyWitness : Term (relationalScope n + 3)}
    (domainTranslation :
      Judgment realizers context domain (.sort level annotation) domain' domainWitness)
    (bodyTranslation :
      Judgment realizers (.extend context domain) body codomain body' bodyWitness) :
    Judgment realizers context (.lam domain body) (.pi domain codomain) (.lam domain' body')
      (Term.lambdaWitness domain domain' domainWitness bodyWitness) :=
  .lam domainTranslation bodyTranslation

example {realizers : SyntaxRealizers} {context : Context n}
    {domain domain' codomain codomain' : Term n}
    {level : Nat} {domainAnnotation codomainAnnotation outputAnnotation : Annotation}
    {domainWitness codomainWitness : Term (relationalScope n)}
    (requirements :
      (domainAnnotation, codomainAnnotation) = arrowRequirements outputAnnotation)
    (domainTranslation :
      Judgment realizers context domain (.sort level domainAnnotation) domain' domainWitness)
    (codomainTranslation :
      Judgment realizers context codomain (.sort level codomainAnnotation) codomain'
        codomainWitness) :
    Judgment realizers context (Term.arrow domain codomain) (.sort level outputAnnotation)
      (Term.arrow domain' codomain')
      (realizers.arrow outputAnnotation domain domain' codomain codomain'
        domainWitness codomainWitness) :=
  .arrow requirements domainTranslation codomainTranslation

example {realizers : SyntaxRealizers} {context : Context n} {domain domain' : Term n}
    {codomain codomain' : Term (n + 1)} {level : Nat}
    {domainAnnotation codomainAnnotation outputAnnotation : Annotation}
    {domainWitness : Term (relationalScope n)}
    {codomainWitness : Term (relationalScope n + 3)}
    (requirements :
      (domainAnnotation, codomainAnnotation) =
        dependentProductRequirements outputAnnotation)
    (domainTranslation :
      Judgment realizers context domain (.sort level domainAnnotation) domain' domainWitness)
    (codomainTranslation :
      Judgment realizers (.extend context domain) codomain (.sort level codomainAnnotation)
        codomain' codomainWitness) :
    Judgment realizers context (.pi domain codomain) (.sort level outputAnnotation)
      (.pi domain' codomain')
      (realizers.pi outputAnnotation domain domain' codomain codomain'
        domainWitness codomainWitness) :=
  .pi requirements domainTranslation codomainTranslation

example {realizers : SyntaxRealizers} {context : Context n} {term type type' term' : Term n}
    {termWitness : Term (relationalScope n)}
    (translation : Judgment realizers context term type term' termWitness)
    (subtype : AnnotatedDependentCalculus.Subtype context.gamma type type') :
    Judgment realizers context term type' term'
      (realizers.weakening context subtype termWitness) :=
  .conversion translation subtype

example (realizers : SyntaxRealizers) (bridge : WitnessTypingBridge) : Prop :=
  AbstractionClaim realizers bridge

example {realizers : SyntaxRealizers} {context : Context n}
    {term type term' : Term n} {witness : Term (relationalScope n)}
    (translation : Judgment realizers context term type term' witness) :
    term' = term :=
  translation.primed_eq_source

example : ¬ ContextWitnessRecoveryClaim :=
  not_contextWitnessRecoveryClaim

example (realizers : SyntaxRealizers) (bridge : WitnessTypingBridge) :
    AbstractionClaim realizers bridge ↔ WitnessAbstractionClaim realizers bridge :=
  abstractionClaim_iff_witnessAbstractionClaim realizers bridge

example {realizers : SyntaxRealizers} {context : Context n}
    {realization : ContextRealization context}
    (coherent : ContextRealization.Coherent realizers realization) :
    realization.primedContext = context.gamma :=
  coherent.primedContext_eq_gamma

example (realizers : SyntaxRealizers) (bridge : WitnessTypingBridge) :
    RealizedAbstractionClaim realizers bridge ↔
      RealizedWitnessAbstractionClaim realizers bridge :=
  realizedAbstractionClaim_iff_witnessAbstractionClaim realizers bridge

end DeepWiki.Refine.AnnotatedRelationTranslation
