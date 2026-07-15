import DeepWiki.Refine.AnnotatedCalculusConservativity

/-! # Maximal annotation

Ordinary dependent terms embed into the annotated calculus by assigning the top relation
annotation to every universe. Erasure is a left inverse of this maximal annotation embedding.
-/

set_option linter.defProp false

namespace DeepWiki.Refine.MaximalAnnotation

namespace Term

/-- Assign the fully coherent relation annotation to every universe in an ordinary term. -/
def annotate : DependentCalculus.Term n → AnnotatedDependentCalculus.Term n
  | .sort level => .sort level Annotation.equivalence
  | .var index => .var index
  | .app function argument => .app (annotate function) (annotate argument)
  | .lam domain body => .lam (annotate domain) (annotate body)
  | .pi domain codomain => .pi (annotate domain) (annotate codomain)

/-- Erasing a maximally annotated term returns the original ordinary term. -/
@[simp] theorem erase_annotate (term : DependentCalculus.Term n) :
    (annotate term).erase = term := by
  induction term with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [annotate, AnnotatedDependentCalculus.Term.erase,
        functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [annotate, AnnotatedDependentCalculus.Term.erase,
        domainInduction, bodyInduction]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [annotate, AnnotatedDependentCalculus.Term.erase,
        domainInduction, codomainInduction]

/-- Maximal annotation commutes with intrinsically scoped renaming. -/
@[simp] theorem annotate_rename (term : DependentCalculus.Term source)
    (mapping : DependentCalculus.Renaming source target) :
    annotate (term.rename mapping) = (annotate term).rename mapping := by
  induction term generalizing target with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [DependentCalculus.Term.rename, annotate,
        AnnotatedDependentCalculus.Term.rename, functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [DependentCalculus.Term.rename, annotate,
        AnnotatedDependentCalculus.Term.rename, domainInduction, bodyInduction]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [DependentCalculus.Term.rename, annotate,
        AnnotatedDependentCalculus.Term.rename, domainInduction, codomainInduction]

end Term

namespace Substitution

/-- Maximally annotate every term in an ordinary simultaneous substitution. -/
def annotate (mapping : DependentCalculus.Substitution source target) :
    AnnotatedDependentCalculus.Substitution source target :=
  fun index => Term.annotate (mapping index)

/-- Maximal annotation sends single substitution to annotated single substitution. -/
@[simp] theorem annotate_single (argument : DependentCalculus.Term n) :
    annotate (DependentCalculus.Substitution.single argument) =
      AnnotatedDependentCalculus.Substitution.single (Term.annotate argument) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

/-- Maximal annotation commutes with lifting a substitution beneath a binder. -/
@[simp] theorem annotate_lift (mapping : DependentCalculus.Substitution source target) :
    annotate (DependentCalculus.Substitution.lift mapping) =
      AnnotatedDependentCalculus.Substitution.lift (annotate mapping) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro older
  simp [annotate, DependentCalculus.Substitution.lift,
    AnnotatedDependentCalculus.Substitution.lift, Term.annotate_rename]

end Substitution

namespace Term

/-- Maximal annotation commutes with capture-avoiding simultaneous substitution. -/
@[simp] theorem annotate_substitute (term : DependentCalculus.Term source)
    (mapping : DependentCalculus.Substitution source target) :
    annotate (term.substitute mapping) =
      (annotate term).substitute (Substitution.annotate mapping) := by
  induction term generalizing target with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [DependentCalculus.Term.substitute, annotate,
        AnnotatedDependentCalculus.Term.substitute,
        functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [DependentCalculus.Term.substitute, annotate,
        AnnotatedDependentCalculus.Term.substitute,
        domainInduction, bodyInduction, Substitution.annotate_lift]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [DependentCalculus.Term.substitute, annotate,
        AnnotatedDependentCalculus.Term.substitute,
        domainInduction, codomainInduction, Substitution.annotate_lift]

/-- Maximal annotation commutes with single-variable instantiation. -/
@[simp] theorem annotate_instantiate (body : DependentCalculus.Term (n + 1))
    (argument : DependentCalculus.Term n) :
    annotate (body.instantiate argument) =
      (annotate body).instantiate (annotate argument) := by
  simp [DependentCalculus.Term.instantiate, AnnotatedDependentCalculus.Term.instantiate,
    annotate_substitute, Substitution.annotate_single]

end Term

namespace Context

/-- Maximally annotate every declaration in an ordinary dependent context. -/
def annotate : DependentCalculus.Context n → AnnotatedDependentCalculus.Context n
  | .empty => .empty
  | .extend context type => .extend (annotate context) (Term.annotate type)

/-- Erasing a maximally annotated context returns the original context. -/
@[simp] theorem erase_annotate (context : DependentCalculus.Context n) :
    (annotate context).erase = context := by
  induction context with
  | empty => rfl
  | extend context type inductionHypothesis =>
      simp only [annotate, AnnotatedDependentCalculus.Context.erase,
        inductionHypothesis, Term.erase_annotate]

/-- Lookup commutes with maximal annotation of a dependent context. -/
@[simp] theorem annotate_lookup (context : DependentCalculus.Context n) (index : Fin n) :
    Term.annotate (context.lookup index) = (annotate context).lookup index := by
  induction context with
  | empty => exact Fin.elim0 index
  | extend context type inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · simp [DependentCalculus.Context.lookup, AnnotatedDependentCalculus.Context.lookup,
          annotate, Term.annotate_rename]
      · intro older
        simp [DependentCalculus.Context.lookup, AnnotatedDependentCalculus.Context.lookup,
          annotate, Term.annotate_rename, inductionHypothesis]

end Context

/-- Maximal annotation preserves the syntactic shape of ordinary kinds. -/
def isKind {kind : DependentCalculus.Term n} :
    DependentCalculus.IsKind kind →
      AnnotatedDependentCalculus.IsKind (Term.annotate kind)
  | .sort level => .sort level Annotation.equivalence
  | .pi domain codomainKind =>
      .pi (Term.annotate domain) (isKind codomainKind)

/-- Maximal annotation preserves one compatible beta-reduction step. -/
theorem betaStep {left right : DependentCalculus.Term n}
    (step : DependentCalculus.BetaStep left right) :
    AnnotatedDependentCalculus.BetaStep (Term.annotate left) (Term.annotate right) := by
  induction step with
  | beta domain body argument =>
      simpa only [Term.annotate, Term.annotate_instantiate] using
        AnnotatedDependentCalculus.BetaStep.beta
          (Term.annotate domain) (Term.annotate body) (Term.annotate argument)
  | appFunction _ inductionHypothesis => exact .appFunction inductionHypothesis
  | appArgument _ inductionHypothesis => exact .appArgument inductionHypothesis
  | lamDomain _ inductionHypothesis => exact .lamDomain inductionHypothesis
  | lamBody _ inductionHypothesis => exact .lamBody inductionHypothesis
  | piDomain _ inductionHypothesis => exact .piDomain inductionHypothesis
  | piCodomain _ inductionHypothesis => exact .piCodomain inductionHypothesis

/-- Maximal annotation preserves ordinary definitional conversion. -/
theorem convertible {left right : DependentCalculus.Term n}
    (conversion : DependentCalculus.Convertible left right) :
    AnnotatedDependentCalculus.Convertible (Term.annotate left) (Term.annotate right) := by
  induction conversion with
  | refl term => exact .refl (Term.annotate term)
  | beta step => exact .beta (betaStep step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

mutual

  /-- Maximal annotation preserves well-formedness of the literal annotation-free calculus. -/
  def wellFormed {context : UnderlyingDependentCalculus.Context n} :
      UnderlyingDependentCalculus.WellFormed context →
        AnnotatedDependentCalculus.WellFormed (Context.annotate context)
    | .empty => .empty
    | .extend contextWellFormed typeWellTyped =>
        .extend (wellFormed contextWellFormed) (hasType typeWellTyped)

  /-- Maximal annotation lifts every annotation-free typing derivation to the top annotation. -/
  def hasType {context : UnderlyingDependentCalculus.Context n}
      {term type : UnderlyingDependentCalculus.Term n} :
      UnderlyingDependentCalculus.HasType context term type →
        AnnotatedDependentCalculus.HasType (Context.annotate context)
          (Term.annotate term) (Term.annotate type)
    | .sort contextWellFormed level =>
        .sort (wellFormed contextWellFormed)
          (admissibleUniverseTranslation_of_equivalence Annotation.equivalence) level
    | .var contextWellFormed index => by
        simpa only [Term.annotate, Context.annotate_lookup] using
          AnnotatedDependentCalculus.HasType.var (wellFormed contextWellFormed) index
    | .app functionWellTyped argumentWellTyped => by
        simpa only [Term.annotate, Term.annotate_instantiate] using
          AnnotatedDependentCalculus.HasType.app
            (hasType functionWellTyped) (hasType argumentWellTyped)
    | .lam bodyWellTyped =>
        .lam (hasType bodyWellTyped)
    | .arrow domainWellTyped codomainWellTyped => by
        simpa only [UnderlyingDependentCalculus.Term.arrow,
          AnnotatedDependentCalculus.Term.arrow, Term.annotate,
          Term.annotate_rename] using
            AnnotatedDependentCalculus.HasType.arrow
              (hasType domainWellTyped) (hasType codomainWellTyped)
              (show arrowRequirements Annotation.equivalence =
                (Annotation.equivalence, Annotation.equivalence) by rfl)
    | .pi domainWellTyped codomainWellTyped =>
        .pi (hasType domainWellTyped) (hasType codomainWellTyped)
          (show dependentProductRequirements Annotation.equivalence =
            (Annotation.equivalence, Annotation.equivalence) by rfl)
    | .conversion termWellTyped subtype =>
        .conversion (hasType termWellTyped) (subtypeDerivation subtype)

  /-- Maximal annotation lifts annotation-free subtyping derivations componentwise. -/
  def subtypeDerivation {context : UnderlyingDependentCalculus.Context n}
      {left right : UnderlyingDependentCalculus.Term n} :
      UnderlyingDependentCalculus.Subtype context left right →
        AnnotatedDependentCalculus.Subtype (Context.annotate context)
          (Term.annotate left) (Term.annotate right)
    | .conversion kindShape leftWellTyped rightWellTyped equal =>
        .conversion (isKind kindShape) (hasType leftWellTyped) (hasType rightWellTyped)
          (convertible equal)
    | .sort levelOrder =>
        .sort le_rfl levelOrder
    | .app kindShape targetWellTyped functionSubtype =>
        .app (isKind kindShape) (hasType targetWellTyped)
          (subtypeDerivation functionSubtype)
    | .lam bodySubtype =>
        .lam (subtypeDerivation bodySubtype)
    | .pi productWellTyped domainSubtype codomainSubtype =>
        .pi (hasType productWellTyped) (subtypeDerivation domainSubtype)
          (subtypeDerivation codomainSubtype)

end

/-- Erasing a maximally lifted typing derivation recovers the original typing proposition. -/
theorem erase_hasType {context : UnderlyingDependentCalculus.Context n}
    {term type : UnderlyingDependentCalculus.Term n}
    (derivation : UnderlyingDependentCalculus.HasType context term type) :
    UnderlyingDependentCalculus.HasType context term type := by
  simpa only [Context.erase_annotate, Term.erase_annotate] using
    (hasType derivation).erase

example (term : DependentCalculus.Term n) :
    (Term.annotate term).erase = term :=
  Term.erase_annotate term

example (context : DependentCalculus.Context n) :
    (Context.annotate context).erase = context :=
  Context.erase_annotate context

example (body : DependentCalculus.Term (n + 1))
    (argument : DependentCalculus.Term n) :
    Term.annotate (body.instantiate argument) =
      (Term.annotate body).instantiate (Term.annotate argument) :=
  Term.annotate_instantiate body argument

example {kind : DependentCalculus.Term n} (kindShape : DependentCalculus.IsKind kind) :
    AnnotatedDependentCalculus.IsKind (Term.annotate kind) :=
  isKind kindShape

example {left right : DependentCalculus.Term n}
    (conversion : DependentCalculus.Convertible left right) :
    AnnotatedDependentCalculus.Convertible (Term.annotate left) (Term.annotate right) :=
  convertible conversion

end DeepWiki.Refine.MaximalAnnotation
