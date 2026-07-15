import DeepWiki.Refine.AnnotatedDependentCalculus
import DeepWiki.Refine.CCOmega.Confluence

/-! # Erasure of the annotated dependent calculus

The literal erasure of the annotated rules gives its own annotation-free typing and structural
subtyping judgments. These remain separate from ordinary `CCω` cumulativity.
-/

namespace DeepWiki.Refine.UnderlyingDependentCalculus

/-- Annotation-free terms reuse the intrinsically scoped dependent-calculus syntax. -/
abbrev Term := DependentCalculus.Term

/-- Annotation-free contexts reuse intrinsically scoped dependent contexts. -/
abbrev Context := DependentCalculus.Context

namespace Term

/-- A non-dependent arrow is a product whose codomain ignores its bound variable. -/
def arrow (domain codomain : Term n) : Term n :=
  .pi domain (codomain.rename DependentCalculus.Renaming.shift)

end Term

/-- Annotation-free kinds are the ordinary calculus's universes and product kinds. -/
abbrev IsKind {n : Nat} (term : Term n) := DependentCalculus.IsKind term

mutual

  /-- An annotation-free context is well formed when every entry is a universe-typed term. -/
  inductive WellFormed : Context n → Prop where
    /-- The empty context is well formed. -/
    | empty : WellFormed .empty
    /-- Extend a well-formed context by a universe-typed term. -/
    | extend {context : Context n} {type : Term n} {level : Nat}
        (contextWellFormed : WellFormed context)
        (typeWellTyped : HasType context type (.sort level)) :
        WellFormed (.extend context type)

  /-- Annotation-free dependent typing obtained by erasing the rules of `CCω⁺`. -/
  inductive HasType : Context n → Term n → Term n → Prop where
    /-- Every universe is typed by its immediate predicative successor. -/
    | sort {context : Context n} (contextWellFormed : WellFormed context)
        (level : Nat) : HasType context (.sort level) (.sort (level + 1))
    /-- A variable has the type obtained by dependent-context lookup. -/
    | var {context : Context n} (contextWellFormed : WellFormed context)
        (index : Fin n) : HasType context (.var index) (context.lookup index)
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
    /-- An arrow is universe-typed when its domain and codomain inhabit the same universe. -/
    | arrow {context : Context n} {domain codomain : Term n} {level : Nat}
        (domainWellTyped : HasType context domain (.sort level))
        (codomainWellTyped : HasType context codomain (.sort level)) :
        HasType context (Term.arrow domain codomain) (.sort level)
    /-- A dependent product is universe-typed when its domain and codomain share a universe. -/
    | pi {context : Context n} {domain : Term n} {codomain : Term (n + 1)}
        {level : Nat}
        (domainWellTyped : HasType context domain (.sort level))
        (codomainWellTyped : HasType (.extend context domain) codomain (.sort level)) :
        HasType context (.pi domain codomain) (.sort level)
    /-- A term may be assigned any supertype given by annotation-free subtyping. -/
    | conversion {context : Context n} {term type type' : Term n}
        (termWellTyped : HasType context term type)
        (subtype : Subtype context type type') : HasType context term type'

  /-- Annotation-free subtyping obtained by erasing the rules of annotated subtyping. -/
  inductive Subtype : Context n → Term n → Term n → Prop where
    /-- Convertible terms with a common kind are mutually subtypes. -/
    | conversion {context : Context n} {left right kind : Term n}
        (kindShape : IsKind kind)
        (leftWellTyped : HasType context left kind)
        (rightWellTyped : HasType context right kind)
        (equal : DependentCalculus.Convertible left right) :
        Subtype context left right
    /-- A lower universe is a subtype of every universe at least as high. -/
    | sort {context : Context n} {lower upper : Nat}
        (levelOrder : lower ≤ upper) :
        Subtype context (.sort lower) (.sort upper)
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
        (productWellTyped : HasType context (.pi domain codomain) (.sort level))
        (domainSubtype : Subtype context domain' domain)
        (codomainSubtype : Subtype (.extend context domain') codomain codomain') :
        Subtype context (.pi domain codomain) (.pi domain' codomain')

end

end DeepWiki.Refine.UnderlyingDependentCalculus

namespace DeepWiki.Refine.AnnotatedDependentCalculus

/-- Erasing an annotated kind gives an annotation-free kind. -/
theorem IsKind.erase {term : Term n} :
    IsKind term → UnderlyingDependentCalculus.IsKind term.erase
  | .sort level _ => .sort level
  | .pi domain codomainKind => .pi domain.erase codomainKind.erase

mutual

  /-- Erasure preserves well-formed annotated contexts. -/
  theorem WellFormed.erase {context : Context n} :
      WellFormed context → UnderlyingDependentCalculus.WellFormed context.erase
    | .empty => .empty
    | .extend contextWellFormed typeWellTyped =>
        .extend contextWellFormed.erase typeWellTyped.erase

  /-- Erasure preserves every annotated typing derivation. -/
  theorem HasType.erase {context : Context n} {term type : Term n} :
      HasType context term type →
        UnderlyingDependentCalculus.HasType context.erase term.erase type.erase
    | .sort contextWellFormed _ level => .sort contextWellFormed.erase level
    | .var contextWellFormed index => by
        simpa only [AnnotatedDependentCalculus.Term.erase, Context.erase_lookup] using
          UnderlyingDependentCalculus.HasType.var contextWellFormed.erase index
    | .app functionWellTyped argumentWellTyped => by
        simpa only [Term.erase, Term.erase_instantiate] using
          UnderlyingDependentCalculus.HasType.app
            functionWellTyped.erase argumentWellTyped.erase
    | .lam bodyWellTyped => .lam bodyWellTyped.erase
    | .arrow (domain := domain) (codomain := codomain) (level := level)
        domainWellTyped codomainWellTyped _ => by
        simpa only [AnnotatedDependentCalculus.Term.erase_arrow,
          UnderlyingDependentCalculus.Term.arrow,
          AnnotatedDependentCalculus.Term.erase] using
            UnderlyingDependentCalculus.HasType.arrow
              domainWellTyped.erase codomainWellTyped.erase
    | .pi domainWellTyped codomainWellTyped _ =>
        .pi domainWellTyped.erase codomainWellTyped.erase
    | .conversion termWellTyped subtype =>
        .conversion termWellTyped.erase subtype.erase

  /-- Erasure preserves every annotated subtyping derivation. -/
  theorem Subtype.erase {context : Context n} {left right : Term n} :
      Subtype context left right →
        UnderlyingDependentCalculus.Subtype context.erase left.erase right.erase
    | .conversion kindShape leftWellTyped rightWellTyped equal =>
        .conversion kindShape.erase leftWellTyped.erase rightWellTyped.erase equal.erase
    | .sort _ levelOrder => .sort levelOrder
    | .app kindShape targetWellTyped functionSubtype =>
        .app kindShape.erase targetWellTyped.erase functionSubtype.erase
    | .lam bodySubtype => .lam bodySubtype.erase
    | .pi productWellTyped domainSubtype codomainSubtype =>
        .pi productWellTyped.erase domainSubtype.erase codomainSubtype.erase

end

/-- Erasing annotated typing derivations preserves the strengthened annotation-free judgment. -/
theorem typing_erases_to_strengthened {context : Context n} {term type : Term n}
    (derivation : HasType context term type) :
    UnderlyingDependentCalculus.HasType context.erase term.erase type.erase :=
  derivation.erase

/-- Erasing annotated subtyping derivations preserves strengthened annotation-free subtyping. -/
theorem subtyping_erases_to_strengthened {context : Context n} {left right : Term n}
    (derivation : Subtype context left right) :
    UnderlyingDependentCalculus.Subtype context.erase left.erase right.erase :=
  derivation.erase

/-- Erasing annotated context derivations preserves strengthened context formation. -/
theorem context_erases_to_strengthened {context : Context n} (derivation : WellFormed context) :
    UnderlyingDependentCalculus.WellFormed context.erase :=
  derivation.erase

end DeepWiki.Refine.AnnotatedDependentCalculus

namespace DeepWiki.Refine.AnnotatedCalculusConservativity

/-- The ill-formed claim that annotated subtyping erases to beta conversion. -/
def SubtypingErasureAsConversionClaim : Prop :=
  ∀ {n : Nat} {context : AnnotatedDependentCalculus.Context n}
    {left right : AnnotatedDependentCalculus.Term n},
    AnnotatedDependentCalculus.Subtype context left right →
      DependentCalculus.Convertible left.erase right.erase

/-- Universe cumulativity refutes subtyping erasure to beta conversion. -/
theorem not_subtypingErasureAsConversionClaim :
    ¬ SubtypingErasureAsConversionClaim := by
  intro claim
  have annotatedSubtype :
      AnnotatedDependentCalculus.Subtype
        AnnotatedDependentCalculus.Context.empty
        (.sort 0 Annotation.equivalence) (.sort 1 Annotation.equivalence) :=
    .sort (le_refl Annotation.equivalence) (Nat.zero_le 1)
  have conversion := claim annotatedSubtype
  change DependentCalculus.Convertible
    (.sort 0 : DependentCalculus.Term 0) (.sort 1) at conversion
  exact Nat.zero_ne_one conversion.sort_level_eq

/-- The ill-formed claim that annotated typing erases to beta conversion. -/
def AnnotationErasureAsConversionClaim : Prop :=
  ∀ {n : Nat} {context : AnnotatedDependentCalculus.Context n}
    {term type : AnnotatedDependentCalculus.Term n},
    AnnotatedDependentCalculus.HasType context term type →
      DependentCalculus.Convertible term.erase type.erase

/-- Annotated universe typing refutes erasure to beta conversion. -/
theorem not_annotationErasureAsConversionClaim : ¬ AnnotationErasureAsConversionClaim := by
  intro claim
  have annotatedTyping :
      AnnotatedDependentCalculus.HasType
        AnnotatedDependentCalculus.Context.empty
        (.sort 0 Annotation.equivalence) (.sort 1 Annotation.equivalence) :=
    .sort .empty (admissibleUniverseTranslation_of_equivalence _) 0
  have conversion := claim annotatedTyping
  change DependentCalculus.Convertible
    (.sort 0 : DependentCalculus.Term 0) (.sort 1) at conversion
  exact Nat.zero_ne_one conversion.sort_level_eq

/-- Annotation-erasure conservativity maps annotated typing into its literal unannotated calculus. -/
abbrev AnnotationErasureConservativity : Prop :=
  ∀ {n : Nat} {context : AnnotatedDependentCalculus.Context n}
    {term type : AnnotatedDependentCalculus.Term n},
    AnnotatedDependentCalculus.HasType context term type →
      UnderlyingDependentCalculus.HasType context.erase term.erase type.erase

/-- The annotated calculus is conservative over its annotation-free erasure. -/
theorem annotationErasureConservativity : AnnotationErasureConservativity := by
  intro n context term type derivation
  exact derivation.erase

/-- A term is universe-typed in the ordinary dependent calculus. -/
def IsUniverseTyped {n : Nat} (context : DependentCalculus.Context n)
    (term : DependentCalculus.Term n) : Prop :=
  ∃ level, DependentCalculus.HasType context term (.sort level)

/-- Typed conversion at a common kind preserves ordinary universe typehood. -/
def TypedConversionUniverseRegularity : Prop :=
  ∀ {n : Nat} {context : DependentCalculus.Context n}
    {left right kind : DependentCalculus.Term n},
    DependentCalculus.IsKind kind →
      DependentCalculus.HasType context left kind →
      DependentCalculus.HasType context right kind →
      DependentCalculus.Convertible left right →
      IsUniverseTyped context left → IsUniverseTyped context right

/-- Narrowing a dependent context along cumulative domain subtyping preserves typing. -/
def DependentContextNarrowing : Prop :=
  ∀ {n : Nat} {context : DependentCalculus.Context n}
    {domain domain' : DependentCalculus.Term n}
    {term type : DependentCalculus.Term (n + 1)},
    IsUniverseTyped context domain →
      IsUniverseTyped context domain' →
      DependentCalculus.Cumulative domain' domain →
      DependentCalculus.HasType (.extend context domain) term type →
        DependentCalculus.HasType (.extend context domain') term type

example {context : AnnotatedDependentCalculus.Context n}
    {term type : AnnotatedDependentCalculus.Term n}
    (derivation : AnnotatedDependentCalculus.HasType context term type) :
    UnderlyingDependentCalculus.HasType context.erase term.erase type.erase :=
  derivation.erase

example {context : AnnotatedDependentCalculus.Context n}
    {left right : AnnotatedDependentCalculus.Term n}
    (derivation : AnnotatedDependentCalculus.Subtype context left right) :
    UnderlyingDependentCalculus.Subtype context.erase left.erase right.erase :=
  derivation.erase

example : ¬ AnnotationErasureAsConversionClaim :=
  not_annotationErasureAsConversionClaim

example : ¬ SubtypingErasureAsConversionClaim :=
  not_subtypingErasureAsConversionClaim

end DeepWiki.Refine.AnnotatedCalculusConservativity
