import DeepWiki.Refine.AnnotatedDependentCalculus
import DeepWiki.Refine.RawParametricitySyntax
import DeepWiki.Refine.ParametricitySequents

/-! # Scoped annotated proof transfer

An intrinsically scoped synthesis judgment translates annotated dependent terms together with
proof-relevant witnesses. Source and primed terms use parallel scopes; witnesses use the
corresponding three-copy relational scope.
-/

namespace DeepWiki.Refine.AnnotatedRelationTranslation

/-- Terms of the annotated dependent object language. -/
abbrev Term := AnnotatedDependentCalculus.Term

/-- Number of original, primed, and witness variables generated from an `n`-variable scope. -/
abbrev relationalScope (n : Nat) := DependentCalculus.RawParametricity.scopeSize n

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

/-- Object-language quotation data for expressing witness typing in the relational scope. -/
structure WitnessTypingBridge where
  /-- The annotated typing context for the original/prime/witness expansion of a source context. -/
  relationalContext : {n : Nat} →
    Context n → AnnotatedDependentCalculus.Context (relationalScope n)
  /-- Quote application of a relation record to an original and a primed term. -/
  relationType : {n : Nat} →
    Term (relationalScope n) → Term (relationalScope n) →
      Term (relationalScope n) → Term (relationalScope n)

/-- The abstraction conclusion types the primed term and the synthesized relational witness. -/
def AbstractionConclusion (bridge : WitnessTypingBridge) (context : Context n)
    (term term' type' : Term n)
    (termWitness typeWitness : Term (relationalScope n)) : Prop :=
  AnnotatedDependentCalculus.HasType context.gamma term' type' ∧
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

end DeepWiki.Refine.AnnotatedRelationTranslation
