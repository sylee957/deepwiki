import DeepWiki.Refine.AnnotatedDependentCalculus
import DeepWiki.Refine.AnnotatedRelationTranslation

/-! # Intrinsically scoped syntax with registered constants

An intrinsically scoped annotated calculus is parameterized by global constant names. Its
constant environment assigns same-erasure annotated source types and arbitrary closed target and
witness terms. The lookup constructors here are syntactic; their output-typing laws are separate.
-/

namespace DeepWiki.Refine.RegisteredConstantSyntax

open DeepWiki.Refine

/-- Annotation-free terms with genuine global constants and `n` local variables in scope. -/
inductive ErasedTerm (Constant : Type u) : Nat → Type u where
  /-- An annotation-free universe. -/
  | sort {n : Nat} (level : Nat) : ErasedTerm Constant n
  /-- An intrinsically scoped local variable. -/
  | var {n : Nat} (index : Fin n) : ErasedTerm Constant n
  /-- A global constant occurrence. -/
  | constant {n : Nat} (name : Constant) : ErasedTerm Constant n
  /-- Application of two terms. -/
  | app {n : Nat} (function argument : ErasedTerm Constant n) : ErasedTerm Constant n
  /-- A lambda with an explicit domain. -/
  | lam {n : Nat} (domain : ErasedTerm Constant n)
      (body : ErasedTerm Constant (n + 1)) : ErasedTerm Constant n
  /-- A dependent product. -/
  | pi {n : Nat} (domain : ErasedTerm Constant n)
      (codomain : ErasedTerm Constant (n + 1)) : ErasedTerm Constant n
  deriving DecidableEq, Repr

/-- Annotated terms with genuine global constants and `n` local variables in scope. -/
inductive Term (Constant : Type u) : Nat → Type u where
  /-- A universe carrying its relation annotation. -/
  | sort {n : Nat} (level : Nat) (annotation : Annotation) : Term Constant n
  /-- An intrinsically scoped local variable. -/
  | var {n : Nat} (index : Fin n) : Term Constant n
  /-- A genuine global constant occurrence. -/
  | constant {n : Nat} (name : Constant) : Term Constant n
  /-- Application of two annotated terms. -/
  | app {n : Nat} (function argument : Term Constant n) : Term Constant n
  /-- A lambda with an explicit annotated domain. -/
  | lam {n : Nat} (domain : Term Constant n)
      (body : Term Constant (n + 1)) : Term Constant n
  /-- An annotated dependent product. -/
  | pi {n : Nat} (domain : Term Constant n)
      (codomain : Term Constant (n + 1)) : Term Constant n
  deriving DecidableEq, Repr

/-- A de Bruijn renaming between two local scopes. -/
abbrev Renaming (source target : Nat) := DependentCalculus.Renaming source target

namespace ErasedTerm

/-- Rename every local variable while leaving global constants unchanged. -/
def rename (mapping : Renaming source target) :
    ErasedTerm Constant source → ErasedTerm Constant target
  | .sort level => .sort level
  | .var index => .var (mapping index)
  | .constant name => .constant name
  | .app function argument => .app (rename mapping function) (rename mapping argument)
  | .lam domain body =>
      .lam (rename mapping domain) (rename (DependentCalculus.Renaming.lift mapping) body)
  | .pi domain codomain =>
      .pi (rename mapping domain) (rename (DependentCalculus.Renaming.lift mapping) codomain)

end ErasedTerm

namespace Term

/-- Rename every local variable while leaving global constants unchanged. -/
def rename (mapping : Renaming source target) : Term Constant source → Term Constant target
  | .sort level annotation => .sort level annotation
  | .var index => .var (mapping index)
  | .constant name => .constant name
  | .app function argument => .app (rename mapping function) (rename mapping argument)
  | .lam domain body =>
      .lam (rename mapping domain) (rename (DependentCalculus.Renaming.lift mapping) body)
  | .pi domain codomain =>
      .pi (rename mapping domain) (rename (DependentCalculus.Renaming.lift mapping) codomain)

/-- Erase universe annotations while preserving constants, scope, and recursive term structure. -/
def erase : Term Constant n → ErasedTerm Constant n
  | .sort level _ => .sort level
  | .var index => .var index
  | .constant name => .constant name
  | .app function argument => .app function.erase argument.erase
  | .lam domain body => .lam domain.erase body.erase
  | .pi domain codomain => .pi domain.erase codomain.erase

/-- Erasure commutes with intrinsically scoped renaming. -/
@[simp] theorem erase_rename (term : Term Constant source)
    (mapping : Renaming source target) :
    (term.rename mapping).erase = term.erase.rename mapping := by
  induction term generalizing target with
  | sort => rfl
  | var => rfl
  | constant => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [rename, erase, ErasedTerm.rename, functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [rename, erase, ErasedTerm.rename, domainInduction, bodyInduction]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [rename, erase, ErasedTerm.rename, domainInduction, codomainInduction]

/-- Embed the constant-free annotated syntax into the constant-parameterized syntax. -/
def ofCore : AnnotatedDependentCalculus.Term n → Term Constant n
  | .sort level annotation => .sort level annotation
  | .var index => .var index
  | .app function argument => .app (ofCore function) (ofCore argument)
  | .lam domain body => .lam (ofCore domain) (ofCore body)
  | .pi domain codomain => .pi (ofCore domain) (ofCore codomain)

/-- A genuine constant occurrence is never an embedded constant-free term. -/
theorem constant_ne_ofCore (name : Constant) (term : AnnotatedDependentCalculus.Term n) :
    (.constant name : Term Constant n) ≠ ofCore term := by
  cases term <;> simp [ofCore]

/-- A non-dependent arrow is a product whose codomain ignores its bound variable. -/
def arrow (domain codomain : Term Constant n) : Term Constant n :=
  .pi domain (codomain.rename DependentCalculus.Renaming.shift)

/-- Weaken a closed term into an arbitrary local scope. -/
def weakenClosed (term : Term Constant 0) (scope : Nat) : Term Constant scope :=
  term.rename Fin.elim0

end Term

/-- A simultaneous substitution by constant-parameterized annotated terms. -/
abbrev Substitution (Constant : Type u) (source target : Nat) :=
  Fin source → Term Constant target

namespace Substitution

/-- Extend a substitution beneath one binder. -/
def lift (substitute : Substitution Constant source target) :
    Substitution Constant (source + 1) (target + 1) :=
  Fin.cases (.var 0)
    (fun index => (substitute index).rename DependentCalculus.Renaming.shift)

/-- Substitute one term for the newest local variable. -/
def single (argument : Term Constant n) : Substitution Constant (n + 1) n :=
  Fin.cases argument Term.var

end Substitution

namespace Term

/-- Perform capture-avoiding simultaneous substitution. -/
def substitute (mapping : Substitution Constant source target) :
    Term Constant source → Term Constant target
  | .sort level annotation => .sort level annotation
  | .var index => mapping index
  | .constant name => .constant name
  | .app function argument =>
      .app (substitute mapping function) (substitute mapping argument)
  | .lam domain body =>
      .lam (substitute mapping domain) (substitute (Substitution.lift mapping) body)
  | .pi domain codomain =>
      .pi (substitute mapping domain) (substitute (Substitution.lift mapping) codomain)

/-- Instantiate the newest local variable. -/
def instantiate (body : Term Constant (n + 1)) (argument : Term Constant n) :
    Term Constant n :=
  body.substitute (Substitution.single argument)

end Term

/-- A dependent context whose types may themselves contain global constants. -/
inductive Context (Constant : Type u) : Nat → Type u where
  /-- The empty context. -/
  | empty : Context Constant 0
  /-- Extend a context by a type in the preceding scope. -/
  | extend {n : Nat} (context : Context Constant n) (type : Term Constant n) :
      Context Constant (n + 1)
  deriving DecidableEq, Repr

namespace Context

/-- Look up a local variable's type and weaken it into the ambient context. -/
def lookup : (context : Context Constant n) → Fin n → Term Constant n
  | .empty, index => Fin.elim0 index
  | .extend context type, index =>
      Fin.cases (type.rename DependentCalculus.Renaming.shift)
        (fun older => (context.lookup older).rename DependentCalculus.Renaming.shift) index

end Context

/-- A constant environment over the same recursive syntax used by object terms. -/
structure Environment (Constant : Type u) where
  /-- The names admitted as global constants. -/
  declared : Constant → Prop
  /-- The annotated closed types admitted for each global constant. -/
  annotatedType : Constant → Term Constant 0 → Prop
  /-- All annotated types of a fixed constant have one common annotation erasure. -/
  sameErasure : ∀ {constant type₁ type₂},
    annotatedType constant type₁ → annotatedType constant type₂ →
      type₁.erase = type₂.erase
  /-- Look up arbitrary closed target and relation-witness terms at one annotated type. -/
  translation : Constant → Term Constant 0 →
    Option (Term Constant 0 × Term Constant 0)
  /-- Every successful lookup is attached to a declared constant and an admitted type. -/
  translationSourceValid : ∀ {constant type primed witness},
    translation constant type = some (primed, witness) →
      declared constant ∧ annotatedType constant type

/-- A constant/type choice is stuck when its exact translation lookup is absent. -/
def Environment.IsStuck (environment : Environment Constant) (constant : Constant)
    (type : Term Constant 0) : Prop :=
  environment.translation constant type = none

/-- Stuckness is exactly the absence of an output pair at the selected lookup key. -/
theorem Environment.isStuck_iff_no_lookup (environment : Environment Constant)
    (constant : Constant) (type : Term Constant 0) :
    environment.IsStuck constant type ↔
      ¬ ∃ primed witness,
        environment.translation constant type = some (primed, witness) := by
  constructor
  · intro stuck
    rintro ⟨primed, witness, lookup⟩
    change environment.translation constant type = none at stuck
    rw [stuck] at lookup
    contradiction
  · intro noLookup
    unfold Environment.IsStuck
    cases lookup : environment.translation constant type with
    | none => rfl
    | some output =>
        obtain ⟨primed, witness⟩ := output
        exact (noLookup ⟨primed, witness, lookup⟩).elim

/-- The positive constant rule selects one annotated type from the constant's collection. -/
inductive PositiveTyping (environment : Environment Constant) :
    {n : Nat} → Context Constant n → Constant → Term Constant 0 → Prop where
  /-- A declared constant has every annotated type admitted by its collection. -/
  | constant {n : Nat} {context : Context Constant n} {name : Constant}
      {type : Term Constant 0}
      (nameDeclared : environment.declared name)
      (typeAllowed : environment.annotatedType name type) :
      PositiveTyping environment context name type

/-- Positive constant typing exposes declaration of the source constant. -/
theorem PositiveTyping.declared
    {environment : Environment Constant} {context : Context Constant n}
    {constant : Constant} {type : Term Constant 0}
    (typing : PositiveTyping environment context constant type) :
    environment.declared constant := by
  cases typing with
  | constant nameDeclared _ => exact nameDeclared

/-- Positive constant typing exposes membership of the selected annotated type. -/
theorem PositiveTyping.annotatedType
    {environment : Environment Constant} {context : Context Constant n}
    {constant : Constant} {type : Term Constant 0}
    (typing : PositiveTyping environment context constant type) :
    environment.annotatedType constant type := by
  cases typing with
  | constant _ typeAllowed => exact typeAllowed

/-- Two positive type assignments for one constant have the same annotation erasure. -/
theorem PositiveTyping.erase_eq
    {environment : Environment Constant}
    {context₁ : Context Constant n₁} {context₂ : Context Constant n₂}
    {constant : Constant} {type₁ type₂ : Term Constant 0}
    (first : PositiveTyping environment context₁ constant type₁)
    (second : PositiveTyping environment context₂ constant type₂) :
    type₁.erase = type₂.erase := by
  cases first with
  | constant _ firstAllowed =>
      cases second with
      | constant _ secondAllowed =>
          exact environment.sameErasure firstAllowed secondAllowed

/-- One compatible beta-reduction step on constant-parameterized terms. -/
inductive BetaStep : Term Constant n → Term Constant n → Prop where
  /-- Contract a beta redex. -/
  | beta (domain : Term Constant n) (body : Term Constant (n + 1))
      (argument : Term Constant n) :
      BetaStep (.app (.lam domain body) argument) (body.instantiate argument)
  /-- Reduce the function of an application. -/
  | appFunction {function function' argument : Term Constant n}
      (step : BetaStep function function') :
      BetaStep (.app function argument) (.app function' argument)
  /-- Reduce the argument of an application. -/
  | appArgument {function argument argument' : Term Constant n}
      (step : BetaStep argument argument') :
      BetaStep (.app function argument) (.app function argument')
  /-- Reduce the domain of a lambda. -/
  | lamDomain {domain domain' : Term Constant n} {body : Term Constant (n + 1)}
      (step : BetaStep domain domain') : BetaStep (.lam domain body) (.lam domain' body)
  /-- Reduce beneath a lambda. -/
  | lamBody {domain : Term Constant n} {body body' : Term Constant (n + 1)}
      (step : BetaStep body body') : BetaStep (.lam domain body) (.lam domain body')
  /-- Reduce the domain of a product. -/
  | piDomain {domain domain' : Term Constant n} {codomain : Term Constant (n + 1)}
      (step : BetaStep domain domain') : BetaStep (.pi domain codomain) (.pi domain' codomain)
  /-- Reduce beneath a product binder. -/
  | piCodomain {domain : Term Constant n} {codomain codomain' : Term Constant (n + 1)}
      (step : BetaStep codomain codomain') :
      BetaStep (.pi domain codomain) (.pi domain codomain')

/-- Definitional conversion is the equivalence closure of beta reduction. -/
inductive Convertible : Term Constant n → Term Constant n → Prop where
  /-- Every term is convertible to itself. -/
  | refl (term : Term Constant n) : Convertible term term
  /-- Every beta step is a conversion. -/
  | beta {left right : Term Constant n} (step : BetaStep left right) :
      Convertible left right
  /-- Conversion is symmetric. -/
  | symm {left right : Term Constant n} (conversion : Convertible left right) :
      Convertible right left
  /-- Conversion is transitive. -/
  | trans {first second third : Term Constant n}
      (firstSecond : Convertible first second) (secondThird : Convertible second third) :
      Convertible first third

/-- Kinds are universes or products whose codomain is a kind. -/
inductive IsKind : Term Constant n → Prop where
  /-- Every annotated universe is a kind. -/
  | sort (level : Nat) (annotation : Annotation) :
      IsKind (.sort level annotation : Term Constant n)
  /-- A product ending in a kind is a kind. -/
  | pi (domain : Term Constant n) {codomain : Term Constant (n + 1)}
      (codomainKind : IsKind codomain) : IsKind (.pi domain codomain)

mutual

  /-- A context is well formed relative to a fixed global constant environment. -/
  inductive WellFormed (environment : Environment Constant) : Context Constant n → Prop where
    /-- The empty context is well formed. -/
    | empty : WellFormed environment .empty
    /-- Extend a well-formed context by a universe-typed term. -/
    | extend {context : Context Constant n} {type : Term Constant n} {level : Nat}
        {annotation : Annotation}
        (contextWellFormed : WellFormed environment context)
        (typeWellTyped : HasType environment context type (.sort level annotation)) :
        WellFormed environment (.extend context type)

  /-- Annotated dependent typing over the recursive syntax with global constants. -/
  inductive HasType (environment : Environment Constant) :
      Context Constant n → Term Constant n → Term Constant n → Prop where
    /-- Admissible universe dependencies type annotated sorts. -/
    | sort {context : Context Constant n} (contextWellFormed : WellFormed environment context)
        {source target : Annotation}
        (admissible : AdmissibleUniverseTranslation source target) (level : Nat) :
        HasType environment context (.sort level source) (.sort (level + 1) target)
    /-- A local variable has its dependent-context lookup type. -/
    | var {context : Context Constant n} (contextWellFormed : WellFormed environment context)
        (index : Fin n) :
        HasType environment context (.var index) (context.lookup index)
    /-- The positive global-constant rule assigns the selected closed annotated type. -/
    | constant {context : Context Constant n} {name : Constant} {type : Term Constant 0}
        (typing : PositiveTyping environment context name type) :
        HasType environment context (.constant name) (type.weakenClosed n)
    /-- Application instantiates its dependent codomain. -/
    | app {context : Context Constant n} {function argument domain : Term Constant n}
        {codomain : Term Constant (n + 1)}
        (functionWellTyped : HasType environment context function (.pi domain codomain))
        (argumentWellTyped : HasType environment context argument domain) :
        HasType environment context (.app function argument) (codomain.instantiate argument)
    /-- A lambda is typed by a dependent product. -/
    | lam {context : Context Constant n} {domain : Term Constant n}
        {body codomain : Term Constant (n + 1)}
        (bodyWellTyped : HasType environment (.extend context domain) body codomain) :
        HasType environment context (.lam domain body) (.pi domain codomain)
    /-- A non-dependent arrow follows the output annotation's dependency requirements. -/
    | arrow {context : Context Constant n} {domain codomain : Term Constant n}
        {level : Nat}
        {domainAnnotation codomainAnnotation outputAnnotation : Annotation}
        (domainWellTyped : HasType environment context domain (.sort level domainAnnotation))
        (codomainWellTyped : HasType environment context codomain (.sort level codomainAnnotation))
        (requirements : arrowRequirements outputAnnotation =
          (domainAnnotation, codomainAnnotation)) :
        HasType environment context (Term.arrow domain codomain)
          (.sort level outputAnnotation)
    /-- A dependent product follows the output annotation's dependency requirements. -/
    | pi {context : Context Constant n} {domain : Term Constant n}
        {codomain : Term Constant (n + 1)} {level : Nat}
        {domainAnnotation codomainAnnotation outputAnnotation : Annotation}
        (domainWellTyped : HasType environment context domain (.sort level domainAnnotation))
        (codomainWellTyped :
          HasType environment (.extend context domain) codomain
            (.sort level codomainAnnotation))
        (requirements : dependentProductRequirements outputAnnotation =
          (domainAnnotation, codomainAnnotation)) :
        HasType environment context (.pi domain codomain) (.sort level outputAnnotation)
    /-- A term may be assigned any annotated supertype. -/
    | conversion {context : Context Constant n} {term type type' : Term Constant n}
        (termWellTyped : HasType environment context term type)
        (subtype : Subtype environment context type type') :
        HasType environment context term type'

  /-- Annotated subtyping over the recursive syntax with global constants. -/
  inductive Subtype (environment : Environment Constant) :
      Context Constant n → Term Constant n → Term Constant n → Prop where
    /-- Convertible terms sharing a kind are mutually subtypes. -/
    | conversion {context : Context Constant n} {left right kind : Term Constant n}
        (kindShape : IsKind kind)
        (leftWellTyped : HasType environment context left kind)
        (rightWellTyped : HasType environment context right kind)
        (equal : Convertible left right) : Subtype environment context left right
    /-- A more structured lower sort is a subtype of a weaker higher sort. -/
    | sort {context : Context Constant n} {source target : Annotation} {lower upper : Nat}
        (annotationOrder : target ≤ source) (levelOrder : lower ≤ upper) :
        Subtype environment context (.sort lower source) (.sort upper target)
    /-- Application is covariant in its function. -/
    | app {context : Context Constant n} {function function' argument kind : Term Constant n}
        (kindShape : IsKind kind)
        (targetWellTyped : HasType environment context (.app function' argument) kind)
        (functionSubtype : Subtype environment context function function') :
        Subtype environment context (.app function argument) (.app function' argument)
    /-- Lambda subtyping is covariant beneath an unchanged binder. -/
    | lam {context : Context Constant n} {domain : Term Constant n}
        {body body' : Term Constant (n + 1)}
        (bodySubtype : Subtype environment (.extend context domain) body body') :
        Subtype environment context (.lam domain body) (.lam domain body')
    /-- Product subtyping is contravariant in domains and covariant in codomains. -/
    | pi {context : Context Constant n} {domain domain' : Term Constant n}
        {codomain codomain' : Term Constant (n + 1)} {level : Nat}
        {outputAnnotation : Annotation}
        (productWellTyped :
          HasType environment context (.pi domain codomain) (.sort level outputAnnotation))
        (domainSubtype : Subtype environment context domain' domain)
        (codomainSubtype :
          Subtype environment (.extend context domain') codomain codomain') :
        Subtype environment context (.pi domain codomain) (.pi domain' codomain')

end

/-- A constant environment is source-lawful when every admitted source type inhabits a universe. -/
structure LawfulEnvironment (environment : Environment Constant) : Prop where
  /-- Every admitted annotated constant type is a well-typed closed type. -/
  annotatedTypeWellTyped : ∀ {constant type}, environment.annotatedType constant type →
    ∃ level annotation,
      HasType environment Context.empty type (.sort level annotation)

/-- A lawful environment makes every positively selected constant type universe-typed. -/
theorem PositiveTyping.typeWellTyped
    {environment : Environment Constant} (lawful : LawfulEnvironment environment)
    {context : Context Constant n} {constant : Constant} {type : Term Constant 0}
    (typing : PositiveTyping environment context constant type) :
    ∃ level annotation,
      HasType environment Context.empty type (.sort level annotation) :=
  lawful.annotatedTypeWellTyped typing.annotatedType

/-- A proof-transfer context stores the source types of its local variables. -/
inductive TranslationContext (Constant : Type u) : Nat → Type u where
  /-- The empty proof-transfer context. -/
  | empty : TranslationContext Constant 0
  /-- Extend a proof-transfer context by one source type. -/
  | extend {n : Nat} (context : TranslationContext Constant n) (sourceType : Term Constant n) :
      TranslationContext Constant (n + 1)
  deriving DecidableEq, Repr

namespace TranslationContext

/-- Forget translation data to the source typing context. -/
def gamma : TranslationContext Constant n → Context Constant n
  | .empty => .empty
  | .extend context sourceType => .extend context.gamma sourceType

/-- The source, prime, and witness indices associated with one local variable. -/
structure Entry (Constant : Type u) (n : Nat) where
  /-- The original local-variable index. -/
  original : Fin n
  /-- The original variable's source type. -/
  sourceType : Term Constant n
  /-- The corresponding primed-variable index. -/
  primed : Fin n
  /-- The corresponding witness-variable index. -/
  witness : Fin (AnnotatedRelationTranslation.relationalScope n)
  deriving DecidableEq, Repr

/-- Build the canonical source/prime/witness entry for one local variable. -/
def entryAt (context : TranslationContext Constant n) (index : Fin n) : Entry Constant n where
  original := index
  sourceType := context.gamma.lookup index
  primed := index
  witness := DependentCalculus.RawParametricity.witnessRenaming n index

/-- A translation-context entry is canonical for some source index. -/
def Contains (context : TranslationContext Constant n) (entry : Entry Constant n) : Prop :=
  ∃ index, context.entryAt index = entry

end TranslationContext

namespace Term

/-- Rename a term into the original-variable part of the relational scope. -/
def original (term : Term Constant n) :
    Term Constant (AnnotatedRelationTranslation.relationalScope n) :=
  term.rename (DependentCalculus.RawParametricity.originalRenaming n)

/-- Rename a term into the primed-variable part of the relational scope. -/
def primed (term : Term Constant n) :
    Term Constant (AnnotatedRelationTranslation.relationalScope n) :=
  term.rename (DependentCalculus.RawParametricity.primedRenaming n)

/-- Weaken a term by a specified number of fresh local variables. -/
def weakenBy (term : Term Constant n) : (amount : Nat) → Term Constant (n + amount)
  | 0 => term
  | amount + 1 => (weakenBy term amount).rename DependentCalculus.Renaming.shift

/-- Apply a function witness to original, primed, and witness arguments. -/
def applyWitness
    (functionWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n))
    (argument argument' : Term Constant n)
    (argumentWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n)) :
    Term Constant (AnnotatedRelationTranslation.relationalScope n) :=
  .app (.app (.app functionWitness argument.original) argument'.primed) argumentWitness

/-- Form the relation type of two new endpoints using a domain witness. -/
def relatedDomain
    (domainWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n)) :
    Term Constant (AnnotatedRelationTranslation.relationalScope n + 2) :=
  .app (.app (domainWitness.weakenBy 2) (.var 1)) (.var 0)

/-- Abstract a body witness over original, primed, and witness variables. -/
def lambdaWitness (domain domain' : Term Constant n)
    (domainWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n))
    (bodyWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n + 3)) :
    Term Constant (AnnotatedRelationTranslation.relationalScope n) :=
  .lam domain.original
    (.lam (domain'.primed.weakenBy 1)
      (.lam domainWitness.relatedDomain bodyWitness))

end Term

/-- Fixed object-language realizers for proof transfer in one global environment. -/
structure SyntaxRealizers (environment : Environment Constant) where
  /-- Realize an admissible universe relation witness. -/
  universeRule : {n : Nat} → Annotation → Annotation → Nat →
    Term Constant (AnnotatedRelationTranslation.relationalScope n)
  /-- Realize an annotation-indexed non-dependent arrow witness. -/
  arrow : {n : Nat} → Annotation →
    Term Constant n → Term Constant n → Term Constant n → Term Constant n →
    Term Constant (AnnotatedRelationTranslation.relationalScope n) →
    Term Constant (AnnotatedRelationTranslation.relationalScope n) →
    Term Constant (AnnotatedRelationTranslation.relationalScope n)
  /-- Realize an annotation-indexed dependent-product witness. -/
  pi : {n : Nat} → Annotation →
    Term Constant n → Term Constant n →
    Term Constant (n + 1) → Term Constant (n + 1) →
    Term Constant (AnnotatedRelationTranslation.relationalScope n) →
    Term Constant (AnnotatedRelationTranslation.relationalScope n + 3) →
    Term Constant (AnnotatedRelationTranslation.relationalScope n)
  /-- Realize recursive witness weakening along one annotated subtyping derivation. -/
  weakening : {n : Nat} → (context : TranslationContext Constant n) →
    {source target : Term Constant n} →
    Subtype environment context.gamma source target →
    Term Constant (AnnotatedRelationTranslation.relationalScope n) →
    Term Constant (AnnotatedRelationTranslation.relationalScope n)

/-- Proof-transfer synthesis over the recursively constant-parameterized syntax. -/
inductive Judgment (environment : Environment Constant) (realizers : SyntaxRealizers environment) :
    (context : TranslationContext Constant n) →
    Term Constant n → Term Constant n → Term Constant n →
    Term Constant (AnnotatedRelationTranslation.relationalScope n) → Prop where
  /-- Admissible universe annotations synthesize the selected universe witness. -/
  | sort {context : TranslationContext Constant n} {source target : Annotation}
      (admissible : AdmissibleUniverseTranslation source target) (level : Nat) :
      Judgment environment realizers context (.sort level source) (.sort (level + 1) target)
        (.sort level source) (realizers.universeRule source target level)
  /-- A canonical context entry translates to its primed and witness variables. -/
  | var {context : TranslationContext Constant n}
      {entry : TranslationContext.Entry Constant n}
      (member : context.Contains entry)
      (contextWellFormed : WellFormed environment context.gamma) :
      Judgment environment realizers context (.var entry.original) entry.sourceType
        (.var entry.primed) (.var entry.witness)
  /-- Application applies the translated function and its witness. -/
  | app {context : TranslationContext Constant n}
      {function function' argument argument' domain : Term Constant n}
      {codomain : Term Constant (n + 1)}
      {functionWitness argumentWitness :
        Term Constant (AnnotatedRelationTranslation.relationalScope n)}
      (functionTranslation :
        Judgment environment realizers context function (.pi domain codomain)
          function' functionWitness)
      (argumentTranslation :
        Judgment environment realizers context argument domain argument' argumentWitness) :
      Judgment environment realizers context (.app function argument)
        (codomain.instantiate argument) (.app function' argument')
        (functionWitness.applyWitness argument argument' argumentWitness)
  /-- Lambda synthesis recursively translates its domain and body. -/
  | lam {context : TranslationContext Constant n} {domain domain' : Term Constant n}
      {body codomain body' : Term Constant (n + 1)} {level : Nat}
      {annotation : Annotation}
      {domainWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n)}
      {bodyWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n + 3)}
      (domainTranslation :
        Judgment environment realizers context domain (.sort level annotation)
          domain' domainWitness)
      (bodyTranslation :
        Judgment environment realizers (.extend context domain) body codomain body' bodyWitness) :
      Judgment environment realizers context (.lam domain body) (.pi domain codomain)
        (.lam domain' body') (Term.lambdaWitness domain domain' domainWitness bodyWitness)
  /-- Non-dependent arrows use the displayed annotation requirements. -/
  | arrow {context : TranslationContext Constant n}
      {domain domain' codomain codomain' : Term Constant n} {level : Nat}
      {domainAnnotation codomainAnnotation outputAnnotation : Annotation}
      {domainWitness codomainWitness :
        Term Constant (AnnotatedRelationTranslation.relationalScope n)}
      (requirements :
        (domainAnnotation, codomainAnnotation) = arrowRequirements outputAnnotation)
      (domainTranslation :
        Judgment environment realizers context domain (.sort level domainAnnotation)
          domain' domainWitness)
      (codomainTranslation :
        Judgment environment realizers context codomain (.sort level codomainAnnotation)
          codomain' codomainWitness) :
      Judgment environment realizers context (Term.arrow domain codomain)
        (.sort level outputAnnotation) (Term.arrow domain' codomain')
        (realizers.arrow outputAnnotation domain domain' codomain codomain'
          domainWitness codomainWitness)
  /-- Dependent products use the displayed annotation requirements. -/
  | pi {context : TranslationContext Constant n} {domain domain' : Term Constant n}
      {codomain codomain' : Term Constant (n + 1)} {level : Nat}
      {domainAnnotation codomainAnnotation outputAnnotation : Annotation}
      {domainWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n)}
      {codomainWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n + 3)}
      (requirements :
        (domainAnnotation, codomainAnnotation) =
          dependentProductRequirements outputAnnotation)
      (domainTranslation :
        Judgment environment realizers context domain (.sort level domainAnnotation)
          domain' domainWitness)
      (codomainTranslation :
        Judgment environment realizers (.extend context domain) codomain
          (.sort level codomainAnnotation) codomain' codomainWitness) :
      Judgment environment realizers context (.pi domain codomain)
        (.sort level outputAnnotation) (.pi domain' codomain')
        (realizers.pi outputAnnotation domain domain' codomain codomain'
          domainWitness codomainWitness)
  /-- Conversion weakens the synthesized witness along annotated subtyping. -/
  | conversion {context : TranslationContext Constant n}
      {term type type' term' : Term Constant n}
      {termWitness : Term Constant (AnnotatedRelationTranslation.relationalScope n)}
      (translation : Judgment environment realizers context term type term' termWitness)
      (subtype : Subtype environment context.gamma type type') :
      Judgment environment realizers context term type' term'
        (realizers.weakening context subtype termWitness)
  /-- A registered constant lookup returns arbitrary closed target and witness terms. -/
  | constant {context : TranslationContext Constant n} {name : Constant}
      {type primed witness : Term Constant 0}
      (lookup : environment.translation name type = some (primed, witness)) :
      Judgment environment realizers context (.constant name) (type.weakenClosed n)
        (primed.weakenClosed n)
        (witness.weakenClosed (AnnotatedRelationTranslation.relationalScope n))

/-- A registered constant translation always induces the positive constant-typing premise. -/
theorem Judgment.constant_sourceTyping
    {environment : Environment Constant}
    {context : TranslationContext Constant n} {name : Constant}
    {type primed witness : Term Constant 0}
    (lookup : environment.translation name type = some (primed, witness)) :
    PositiveTyping environment context.gamma name type := by
  exact .constant (environment.translationSourceValid lookup).1
    (environment.translationSourceValid lookup).2

/-- A direct lookup inhabits the concrete registered-constant translation rule. -/
theorem Judgment.constant_of_lookup
    {environment : Environment Constant} {realizers : SyntaxRealizers environment}
    {context : TranslationContext Constant n} {name : Constant}
    {type primed witness : Term Constant 0}
    (lookup : environment.translation name type = some (primed, witness)) :
    Judgment environment realizers context (.constant name) (type.weakenClosed n)
      (primed.weakenClosed n)
      (witness.weakenClosed (AnnotatedRelationTranslation.relationalScope n)) :=
  .constant lookup

example (name : Constant) : Term Constant n :=
  .constant name

example {environment : Environment Constant} {context : Context Constant n}
    {name : Constant} {type : Term Constant 0}
    (typing : PositiveTyping environment context name type) :
    HasType environment context (.constant name) (type.weakenClosed n) :=
  .constant typing

example {environment : Environment Constant} {realizers : SyntaxRealizers environment}
    {context : TranslationContext Constant n} {name : Constant}
    {type primed witness : Term Constant 0}
    (lookup : environment.translation name type = some (primed, witness)) :
    Judgment environment realizers context (.constant name) (type.weakenClosed n)
      (primed.weakenClosed n)
      (witness.weakenClosed (AnnotatedRelationTranslation.relationalScope n)) :=
  .constant lookup

end DeepWiki.Refine.RegisteredConstantSyntax
