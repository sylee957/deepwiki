import DeepWiki.Refine.DependencyRequirements
import DeepWiki.Refine.CCOmega.Typing

/-! # Annotated dependent calculus

Intrinsically scoped terms carry relation annotations on universes. Their declarative subtyping
and typing judgments expose the universe, dependent-product, and arrow dependency conditions.
-/

namespace DeepWiki.Refine.AnnotatedDependentCalculus

/-- Annotated terms with `n` variables in scope. -/
inductive Term : Nat → Type where
  /-- A universe level paired with the relation structure available at that universe. -/
  | sort {n : Nat} (level : Nat) (annotation : Annotation) : Term n
  /-- A de Bruijn variable known to be in scope. -/
  | var {n : Nat} (index : Fin n) : Term n
  /-- Application of one annotated term to another. -/
  | app {n : Nat} (function argument : Term n) : Term n
  /-- A lambda abstraction with an explicit domain and one bound variable in its body. -/
  | lam {n : Nat} (domain : Term n) (body : Term (n + 1)) : Term n
  /-- A dependent product with one bound variable in its codomain. -/
  | pi {n : Nat} (domain : Term n) (codomain : Term (n + 1)) : Term n
  deriving DecidableEq, Repr

/-- A renaming of annotated terms is an intrinsically scoped de Bruijn renaming. -/
abbrev Renaming (source target : Nat) :=
  DependentCalculus.Renaming source target

namespace Term

/-- Rename every free variable, lifting the renaming beneath binders. -/
def rename (mapping : Renaming source target) : Term source → Term target
  | .sort level annotation => .sort level annotation
  | .var index => .var (mapping index)
  | .app function argument => .app (rename mapping function) (rename mapping argument)
  | .lam domain body =>
      .lam (rename mapping domain)
        (rename (DependentCalculus.Renaming.lift mapping) body)
  | .pi domain codomain =>
      .pi (rename mapping domain)
        (rename (DependentCalculus.Renaming.lift mapping) codomain)

/-- Erase universe annotations while preserving scope and term structure. -/
def erase : Term n → DependentCalculus.Term n
  | .sort level _ => .sort level
  | .var index => .var index
  | .app function argument => .app function.erase argument.erase
  | .lam domain body => .lam domain.erase body.erase
  | .pi domain codomain => .pi domain.erase codomain.erase

/-- Erasure commutes with intrinsically scoped renaming. -/
@[simp] theorem erase_rename (term : Term source) (mapping : Renaming source target) :
    (term.rename mapping).erase = term.erase.rename mapping := by
  induction term generalizing target with
  | sort => rfl
  | var => rfl
  | app function argument function_ih argument_ih =>
      simp only [rename, erase, DependentCalculus.Term.rename, function_ih, argument_ih]
  | lam domain body domain_ih body_ih =>
      simp only [rename, erase, DependentCalculus.Term.rename, domain_ih, body_ih]
  | pi domain codomain domain_ih codomain_ih =>
      simp only [rename, erase, DependentCalculus.Term.rename, domain_ih, codomain_ih]

/-- A non-dependent arrow is a product whose codomain ignores its bound variable. -/
def arrow (domain codomain : Term n) : Term n :=
  .pi domain (codomain.rename DependentCalculus.Renaming.shift)

/-- Erasure sends an annotated arrow to the corresponding ordinary arrow encoding. -/
@[simp] theorem erase_arrow (domain codomain : Term n) :
    (arrow domain codomain).erase =
      .pi domain.erase (codomain.erase.rename DependentCalculus.Renaming.shift) := by
  simp [arrow, erase]

end Term

/-- A substitution replaces each source variable by an annotated target term. -/
abbrev Substitution (source target : Nat) := Fin source → Term target

namespace Substitution

/-- Extend a substitution beneath one binder without capturing the new variable. -/
def lift (substitute : Substitution source target) :
    Substitution (source + 1) (target + 1) :=
  Fin.cases (.var 0)
    (fun index => (substitute index).rename DependentCalculus.Renaming.shift)

/-- Substitute one annotated term for the newest variable. -/
def single (argument : Term n) : Substitution (n + 1) n :=
  Fin.cases argument Term.var

/-- Erase every term in an annotated substitution. -/
def erase (substitute : Substitution source target) :
    DependentCalculus.Substitution source target :=
  fun index => (substitute index).erase

/-- Erasing a lifted substitution gives the lifted erased substitution. -/
@[simp] theorem erase_lift (substitute : Substitution source target) :
    erase (lift substitute) = DependentCalculus.Substitution.lift (erase substitute) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  simp [lift, erase, Term.erase_rename]

/-- Erasing a single substitution gives ordinary single substitution. -/
@[simp] theorem erase_single (argument : Term n) :
    erase (single argument) = DependentCalculus.Substitution.single argument.erase := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

end Substitution

namespace Term

/-- Perform capture-avoiding simultaneous substitution on an annotated term. -/
def substitute (mapping : Substitution source target) : Term source → Term target
  | .sort level annotation => .sort level annotation
  | .var index => mapping index
  | .app function argument =>
      .app (substitute mapping function) (substitute mapping argument)
  | .lam domain body =>
      .lam (substitute mapping domain)
        (substitute (Substitution.lift mapping) body)
  | .pi domain codomain =>
      .pi (substitute mapping domain)
        (substitute (Substitution.lift mapping) codomain)

/-- Erasure commutes with capture-avoiding substitution. -/
@[simp] theorem erase_substitute (term : Term source)
    (mapping : Substitution source target) :
    (term.substitute mapping).erase =
      term.erase.substitute (Substitution.erase mapping) := by
  induction term generalizing target with
  | sort => rfl
  | var => rfl
  | app function argument function_ih argument_ih =>
      simp only [substitute, erase, DependentCalculus.Term.substitute,
        function_ih, argument_ih]
  | lam domain body domain_ih body_ih =>
      simp only [substitute, erase, DependentCalculus.Term.substitute,
        domain_ih, body_ih, Substitution.erase_lift]
  | pi domain codomain domain_ih codomain_ih =>
      simp only [substitute, erase, DependentCalculus.Term.substitute,
        domain_ih, codomain_ih, Substitution.erase_lift]

/-- Instantiate the newest variable of an annotated term. -/
def instantiate (body : Term (n + 1)) (argument : Term n) : Term n :=
  body.substitute (Substitution.single argument)

/-- Erasure commutes with single-variable instantiation. -/
@[simp] theorem erase_instantiate (body : Term (n + 1)) (argument : Term n) :
    (body.instantiate argument).erase = body.erase.instantiate argument.erase := by
  simp [instantiate, DependentCalculus.Term.instantiate]

end Term

/-- A dependent annotated context whose newest type may mention all preceding variables. -/
inductive Context : Nat → Type where
  /-- The empty annotated context. -/
  | empty : Context 0
  /-- Extend an annotated context by a type in the preceding scope. -/
  | extend {n : Nat} (context : Context n) (type : Term n) : Context (n + 1)
  deriving DecidableEq, Repr

namespace Context

/-- Look up a variable's annotated type and weaken it into the ambient context. -/
def lookup : (context : Context n) → Fin n → Term n
  | .empty, index => Fin.elim0 index
  | .extend context type, index =>
      Fin.cases (type.rename DependentCalculus.Renaming.shift)
        (fun older => (context.lookup older).rename DependentCalculus.Renaming.shift) index

/-- Erase every annotation in a dependent context. -/
def erase : Context n → DependentCalculus.Context n
  | .empty => .empty
  | .extend context type => .extend context.erase type.erase

/-- Erasing a context lookup gives lookup in the erased context. -/
@[simp] theorem erase_lookup (context : Context n) (index : Fin n) :
    (context.lookup index).erase = context.erase.lookup index := by
  induction context with
  | empty => exact Fin.elim0 index
  | extend context type context_ih =>
      refine Fin.cases ?_ ?_ index
      · simp [lookup, erase, Term.erase_rename]
      · intro older
        simp [lookup, erase, Term.erase_rename, context_ih]

end Context

/-- One compatible beta-reduction step on annotated terms. -/
inductive BetaStep : Term n → Term n → Prop where
  /-- Contract a beta redex by capture-avoiding single substitution. -/
  | beta (domain : Term n) (body : Term (n + 1)) (argument : Term n) :
      BetaStep (.app (.lam domain body) argument) (body.instantiate argument)
  /-- Reduce the function of an application. -/
  | appFunction {function function' argument : Term n}
      (step : BetaStep function function') :
      BetaStep (.app function argument) (.app function' argument)
  /-- Reduce the argument of an application. -/
  | appArgument {function argument argument' : Term n}
      (step : BetaStep argument argument') :
      BetaStep (.app function argument) (.app function argument')
  /-- Reduce the domain annotation of a lambda. -/
  | lamDomain {domain domain' : Term n} {body : Term (n + 1)}
      (step : BetaStep domain domain') :
      BetaStep (.lam domain body) (.lam domain' body)
  /-- Reduce beneath a lambda binder. -/
  | lamBody {domain : Term n} {body body' : Term (n + 1)}
      (step : BetaStep body body') :
      BetaStep (.lam domain body) (.lam domain body')
  /-- Reduce the domain of a dependent product. -/
  | piDomain {domain domain' : Term n} {codomain : Term (n + 1)}
      (step : BetaStep domain domain') :
      BetaStep (.pi domain codomain) (.pi domain' codomain)
  /-- Reduce beneath a dependent-product binder. -/
  | piCodomain {domain : Term n} {codomain codomain' : Term (n + 1)}
      (step : BetaStep codomain codomain') :
      BetaStep (.pi domain codomain) (.pi domain codomain')

/-- Annotated conversion is the reflexive, symmetric, transitive closure of beta reduction. -/
inductive Convertible : Term n → Term n → Prop where
  /-- Every annotated term is convertible to itself. -/
  | refl (term : Term n) : Convertible term term
  /-- Every annotated beta step is a conversion. -/
  | beta {left right : Term n} (step : BetaStep left right) : Convertible left right
  /-- Annotated conversion is symmetric. -/
  | symm {left right : Term n} (conversion : Convertible left right) :
      Convertible right left
  /-- Annotated conversion is transitive. -/
  | trans {first second third : Term n}
      (firstSecond : Convertible first second) (secondThird : Convertible second third) :
      Convertible first third

/-- Erasure maps an annotated beta step to an ordinary beta step. -/
theorem BetaStep.erase {left right : Term n} (step : BetaStep left right) :
    DependentCalculus.BetaStep left.erase right.erase := by
  induction step with
  | beta domain body argument =>
      simpa only [Term.erase, Term.erase_instantiate] using
        DependentCalculus.BetaStep.beta domain.erase body.erase argument.erase
  | appFunction _ ih => exact .appFunction ih
  | appArgument _ ih => exact .appArgument ih
  | lamDomain _ ih => exact .lamDomain ih
  | lamBody _ ih => exact .lamBody ih
  | piDomain _ ih => exact .piDomain ih
  | piCodomain _ ih => exact .piCodomain ih

/-- Erasure maps annotated conversion to ordinary definitional conversion. -/
theorem Convertible.erase {left right : Term n} (conversion : Convertible left right) :
    DependentCalculus.Convertible left.erase right.erase := by
  induction conversion with
  | refl term => exact .refl term.erase
  | beta step => exact .beta step.erase
  | symm _ ih => exact ih.symm
  | trans _ _ first_ih second_ih => exact first_ih.trans second_ih

/-- Kinds are annotated universes or dependent products ending in a kind. -/
inductive IsKind : Term n → Prop where
  /-- Every annotated universe is a kind. -/
  | sort (level : Nat) (annotation : Annotation) :
      IsKind (.sort level annotation : Term n)
  /-- A product is a kind when its codomain is a kind. -/
  | pi (domain : Term n) {codomain : Term (n + 1)}
      (codomainKind : IsKind codomain) : IsKind (.pi domain codomain)

mutual

  /-- A context is well formed when each extension is by an annotated universe-typed term. -/
  inductive WellFormed : Context n → Prop where
    /-- The empty annotated context is well formed. -/
    | empty : WellFormed .empty
    /-- Extend a well-formed context by a type inhabiting an annotated universe. -/
    | extend {context : Context n} {type : Term n} {level : Nat}
        {annotation : Annotation}
        (contextWellFormed : WellFormed context)
        (typeWellTyped : HasType context type (.sort level annotation)) :
        WellFormed (.extend context type)

  /-- `HasType Γ term type` is the annotated dependent typing judgment. -/
  inductive HasType : Context n → Term n → Term n → Prop where
    /-- Admissible universe dependencies type an annotated sort by its successor sort. -/
    | sort {context : Context n} (contextWellFormed : WellFormed context)
        {source target : Annotation}
        (admissible : AdmissibleUniverseTranslation source target) (level : Nat) :
        HasType context (.sort level source) (.sort (level + 1) target)
    /-- A variable has the type obtained by annotated dependent-context lookup. -/
    | var {context : Context n} (contextWellFormed : WellFormed context)
        (index : Fin n) :
        HasType context (.var index) (context.lookup index)
    /-- Applying a dependent function instantiates its codomain with the argument. -/
    | app {context : Context n} {function argument domain : Term n}
        {codomain : Term (n + 1)}
        (functionWellTyped : HasType context function (.pi domain codomain))
        (argumentWellTyped : HasType context argument domain) :
        HasType context (.app function argument) (codomain.instantiate argument)
    /-- A lambda has a dependent-product type when its body has the codomain type. -/
    | lam {context : Context n} {domain : Term n} {body codomain : Term (n + 1)}
        (bodyWellTyped : HasType (.extend context domain) body codomain) :
        HasType context (.lam domain body) (.pi domain codomain)
    /-- A non-dependent arrow uses the arrow dependency requirements of its output annotation. -/
    | arrow {context : Context n} {domain codomain : Term n} {level : Nat}
        {domainAnnotation codomainAnnotation outputAnnotation : Annotation}
        (domainWellTyped : HasType context domain (.sort level domainAnnotation))
        (codomainWellTyped : HasType context codomain (.sort level codomainAnnotation))
        (requirements : arrowRequirements outputAnnotation =
          (domainAnnotation, codomainAnnotation)) :
        HasType context (Term.arrow domain codomain) (.sort level outputAnnotation)
    /-- A dependent product uses the product dependency requirements of its output annotation. -/
    | pi {context : Context n} {domain : Term n} {codomain : Term (n + 1)}
        {level : Nat} {domainAnnotation codomainAnnotation outputAnnotation : Annotation}
        (domainWellTyped : HasType context domain (.sort level domainAnnotation))
        (codomainWellTyped :
          HasType (.extend context domain) codomain (.sort level codomainAnnotation))
        (requirements : dependentProductRequirements outputAnnotation =
          (domainAnnotation, codomainAnnotation)) :
        HasType context (.pi domain codomain) (.sort level outputAnnotation)
    /-- A term may be assigned any annotated supertype given by the subtyping judgment. -/
    | conversion {context : Context n} {term type type' : Term n}
        (termWellTyped : HasType context term type)
        (subtype : Subtype context type type') :
        HasType context term type'

  /-- `Subtype Γ left right` is derivation-indexed annotated subtyping. -/
  inductive Subtype : Context n → Term n → Term n → Prop where
    /-- Convertible terms with a common kind are mutually subtypes. -/
    | conversion {context : Context n} {left right kind : Term n}
        (kindShape : IsKind kind)
        (leftWellTyped : HasType context left kind)
        (rightWellTyped : HasType context right kind)
        (equal : Convertible left right) :
        Subtype context left right
    /-- More structured lower universes are subtypes of weaker higher universes. -/
    | sort {context : Context n} {source target : Annotation} {lower upper : Nat}
        (annotationOrder : target ≤ source) (levelOrder : lower ≤ upper) :
        Subtype context (.sort lower source) (.sort upper target)
    /-- Application is covariant in its function while retaining the same argument. -/
    | app {context : Context n} {function function' argument kind : Term n}
        (kindShape : IsKind kind)
        (targetWellTyped : HasType context (.app function' argument) kind)
        (functionSubtype : Subtype context function function') :
        Subtype context (.app function argument) (.app function' argument)
    /-- Lambda subtyping is covariant in bodies under an unchanged domain. -/
    | lam {context : Context n} {domain : Term n} {body body' : Term (n + 1)}
        (bodySubtype : Subtype (.extend context domain) body body') :
        Subtype context (.lam domain body) (.lam domain body')
    /-- Product subtyping is contravariant in domains and covariant in codomains. -/
    | pi {context : Context n} {domain domain' : Term n}
        {codomain codomain' : Term (n + 1)} {level : Nat}
        {outputAnnotation : Annotation}
        (productWellTyped :
          HasType context (.pi domain codomain) (.sort level outputAnnotation))
        (domainSubtype : Subtype context domain' domain)
        (codomainSubtype : Subtype (.extend context domain') codomain codomain') :
        Subtype context (.pi domain codomain) (.pi domain' codomain')

end

example (level : Nat) (annotation : Annotation) : Term 0 :=
  .sort level annotation

example (level : Nat) (annotation : Annotation) :
    (Term.sort level annotation : Term n).erase = .sort level :=
  rfl

example (domain : Term n) (codomain : Term (n + 1)) :
    (Term.pi domain codomain).erase =
      .pi domain.erase codomain.erase :=
  rfl

example (body : Term (n + 1)) (argument : Term n) :
    (body.instantiate argument).erase = body.erase.instantiate argument.erase :=
  Term.erase_instantiate body argument

example (context : Context n) (index : Fin n) :
    (context.lookup index).erase = context.erase.lookup index :=
  Context.erase_lookup context index

example {context : Context n} {left right kind : Term n}
    (kindShape : IsKind kind)
    (leftWellTyped : HasType context left kind)
    (rightWellTyped : HasType context right kind)
    (equal : Convertible left right) :
    Subtype context left right :=
  .conversion kindShape leftWellTyped rightWellTyped equal

example {context : Context n} {source target : Annotation} {lower upper : Nat}
    (annotationOrder : target ≤ source) (levelOrder : lower ≤ upper) :
    Subtype context (.sort lower source) (.sort upper target) :=
  .sort annotationOrder levelOrder

example {context : Context n} {function function' argument kind : Term n}
    (kindShape : IsKind kind)
    (targetWellTyped : HasType context (.app function' argument) kind)
    (functionSubtype : Subtype context function function') :
    Subtype context (.app function argument) (.app function' argument) :=
  .app kindShape targetWellTyped functionSubtype

example {context : Context n} {domain : Term n} {body body' : Term (n + 1)}
    (bodySubtype : Subtype (.extend context domain) body body') :
    Subtype context (.lam domain body) (.lam domain body') :=
  .lam bodySubtype

example {context : Context n} {domain domain' : Term n}
    {codomain codomain' : Term (n + 1)} {level : Nat}
    {outputAnnotation : Annotation}
    (productWellTyped :
      HasType context (.pi domain codomain) (.sort level outputAnnotation))
    (domainSubtype : Subtype context domain' domain)
    (codomainSubtype : Subtype (.extend context domain') codomain codomain') :
    Subtype context (.pi domain codomain) (.pi domain' codomain') :=
  .pi productWellTyped domainSubtype codomainSubtype

example : WellFormed Context.empty :=
  .empty

example {context : Context n} {type : Term n} {level : Nat}
    {annotation : Annotation}
    (contextWellFormed : WellFormed context)
    (typeWellTyped : HasType context type (.sort level annotation)) :
    WellFormed (.extend context type) :=
  .extend contextWellFormed typeWellTyped

example {context : Context n} (contextWellFormed : WellFormed context)
    {source target : Annotation}
    (admissible : AdmissibleUniverseTranslation source target) (level : Nat) :
    HasType context (.sort level source) (.sort (level + 1) target) :=
  .sort contextWellFormed admissible level

example {context : Context n} (contextWellFormed : WellFormed context)
    (index : Fin n) :
    HasType context (.var index) (context.lookup index) :=
  .var contextWellFormed index

example {context : Context n} {function argument domain : Term n}
    {codomain : Term (n + 1)}
    (functionWellTyped : HasType context function (.pi domain codomain))
    (argumentWellTyped : HasType context argument domain) :
    HasType context (.app function argument) (codomain.instantiate argument) :=
  .app functionWellTyped argumentWellTyped

example {context : Context n} {domain : Term n} {body codomain : Term (n + 1)}
    (bodyWellTyped : HasType (.extend context domain) body codomain) :
    HasType context (.lam domain body) (.pi domain codomain) :=
  .lam bodyWellTyped

example {context : Context n} {domain codomain : Term n} {level : Nat}
    {domainAnnotation codomainAnnotation outputAnnotation : Annotation}
    (domainWellTyped : HasType context domain (.sort level domainAnnotation))
    (codomainWellTyped : HasType context codomain (.sort level codomainAnnotation))
    (requirements : arrowRequirements outputAnnotation =
      (domainAnnotation, codomainAnnotation)) :
    HasType context (Term.arrow domain codomain) (.sort level outputAnnotation) :=
  .arrow domainWellTyped codomainWellTyped requirements

example {context : Context n} {domain : Term n} {codomain : Term (n + 1)}
    {level : Nat} {domainAnnotation codomainAnnotation outputAnnotation : Annotation}
    (domainWellTyped : HasType context domain (.sort level domainAnnotation))
    (codomainWellTyped :
      HasType (.extend context domain) codomain (.sort level codomainAnnotation))
    (requirements : dependentProductRequirements outputAnnotation =
      (domainAnnotation, codomainAnnotation)) :
    HasType context (.pi domain codomain) (.sort level outputAnnotation) :=
  .pi domainWellTyped codomainWellTyped requirements

example {context : Context n} {term type type' : Term n}
    (termWellTyped : HasType context term type)
    (subtype : Subtype context type type') :
    HasType context term type' :=
  .conversion termWellTyped subtype

end DeepWiki.Refine.AnnotatedDependentCalculus
