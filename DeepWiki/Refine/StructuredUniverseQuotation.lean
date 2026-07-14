import DeepWiki.Refine.AnnotatedRelationTranslation
import DeepWiki.Refine.UniverseRelationStructure

/-! # Quoted structured universe witnesses

Native universe witnesses are Lean values of type `StructuredRelation`. This module separately
specifies the object-language terms, typing derivations, and projection conversions required to
quote such witnesses; it does not identify native packages with quoted syntax.
-/

namespace DeepWiki.Refine.StructuredUniverseQuotation

/-- Terms in the annotated dependent object language. -/
abbrev Term := AnnotatedDependentCalculus.Term

/-- Contexts in the annotated dependent object language. -/
abbrev Context := AnnotatedDependentCalculus.Context

/-- A typing judgment on annotated intrinsically scoped object terms. -/
abbrev TypingJudgment := {n : Nat} → Context n → Term n → Term n → Prop

/-- A conversion judgment on annotated intrinsically scoped object terms. -/
abbrev ConversionJudgment := {n : Nat} → Term n → Term n → Prop

/-- An annotated object calculus retaining core typing, application, and conversion congruence. -/
structure ObjectCalculusExtension where
  /-- The extended typing judgment. -/
  hasType : TypingJudgment
  /-- The extended definitional-conversion judgment. -/
  convertible : ConversionJudgment
  /-- Every core annotated typing derivation remains valid. -/
  ofHasType : ∀ {n : Nat} {context : Context n} {term type : Term n},
    AnnotatedDependentCalculus.HasType context term type → hasType context term type
  /-- Every core annotated conversion remains valid. -/
  ofConvertible : ∀ {n : Nat} {left right : Term n},
    AnnotatedDependentCalculus.Convertible left right → convertible left right
  /-- Extended typing is closed under dependent application. -/
  app : ∀ {n : Nat} {context : Context n} {function argument domain : Term n}
      {codomain : Term (n + 1)},
    hasType context function (.pi domain codomain) →
      hasType context argument domain →
        hasType context (.app function argument) (codomain.instantiate argument)
  /-- Extended conversion is compatible with application in function position. -/
  appFunction : ∀ {n : Nat} {function function' argument : Term n},
    convertible function function' →
      convertible (.app function argument) (.app function' argument)

/-- Core annotated conversion is compatible with application in function position. -/
theorem coreConvertible_appFunction {function function' argument : Term n}
    (equal : AnnotatedDependentCalculus.Convertible function function') :
    AnnotatedDependentCalculus.Convertible (.app function argument) (.app function' argument) := by
  induction equal with
  | refl => exact .refl _
  | beta step => exact .beta (.appFunction step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- The existing annotated calculus is the identity object-calculus extension. -/
def ObjectCalculusExtension.core : ObjectCalculusExtension where
  hasType := AnnotatedDependentCalculus.HasType
  convertible := AnnotatedDependentCalculus.Convertible
  ofHasType := id
  ofConvertible := id
  app := AnnotatedDependentCalculus.HasType.app
  appFunction := coreConvertible_appFunction

/-- The quoted type `Param^β Type^α Type^α` of a structured universe witness. -/
def universeWitnessType (relationFamily : {n : Nat} → Annotation → Nat → Term n)
    (source target : Annotation) (level : Nat) : Term 0 :=
  .app (.app (relationFamily target (level + 1)) (.sort level source))
    (.sort level source)

/-- The quoted type of a projection from a universe witness to its relation-family type. -/
def universeProjectionType
    (relationFamilyType : {n : Nat} → Annotation → Nat → Term n)
    (relationFamily : {n : Nat} → Annotation → Nat → Term n)
    (source target : Annotation) (level : Nat) : Term 0 :=
  .pi (universeWitnessType relationFamily source target level)
    ((relationFamilyType source level).rename DependentCalculus.Renaming.shift)

/-- Object-language quotations satisfying the structured-universe witness equation. -/
structure Quotation (calculus : ObjectCalculusExtension) where
  /-- The quoted type of each annotation-indexed relation family. -/
  relationFamilyType : {n : Nat} → Annotation → Nat → Term n
  /-- The quoted annotation-indexed relation family `Param^α`. -/
  relationFamily : {n : Nat} → Annotation → Nat → Term n
  /-- The quoted structured universe witness `p□^{α,β}`. -/
  universeWitness : {n : Nat} → Annotation → Annotation → Nat → Term n
  /-- The quoted relation projection specialized to one admissible universe pair. -/
  relationProjection : {n : Nat} → Annotation → Annotation → Nat → Term n
  /-- Every closed relation-family quote has its quoted family type. -/
  relationFamily_hasType : ∀ source level,
    calculus.hasType .empty (relationFamily source level) (relationFamilyType source level)
  /-- Every admissible closed universe witness has the displayed structured-relation type. -/
  universeWitness_hasType : ∀ source target level,
    AdmissibleUniverseTranslation source target →
      calculus.hasType .empty (universeWitness source target level)
        (universeWitnessType relationFamily source target level)
  /-- Every admissible closed relation projection has its specialized function type. -/
  relationProjection_hasType : ∀ source target level,
    AdmissibleUniverseTranslation source target →
      calculus.hasType .empty (relationProjection source target level)
        (universeProjectionType relationFamilyType relationFamily source target level)
  /-- Projecting a quoted witness converts to its source-annotation relation family. -/
  relationProjection_beta : ∀ {n : Nat} (source target : Annotation) (level : Nat),
    AdmissibleUniverseTranslation source target →
      calculus.convertible
        (.app (relationProjection (n := n) source target level)
          (universeWitness (n := n) source target level))
        (relationFamily (n := n) source level)

namespace Quotation

/-- Apply a quoted relation projection to its quoted structured universe witness. -/
def projectedRelation {calculus : ObjectCalculusExtension}
    (quotation : Quotation calculus) {n : Nat}
    (source target : Annotation) (level : Nat) : Term n :=
  .app (quotation.relationProjection source target level)
    (quotation.universeWitness source target level)

/-- Apply the projected relation of a universe witness to two quoted types. -/
def projectedRelationApplication {calculus : ObjectCalculusExtension}
    (quotation : Quotation calculus) (source target : Annotation) (level : Nat)
    (left right : Term n) : Term n :=
  .app (.app (quotation.projectedRelation source target level) left) right

/-- Apply the quoted source-annotation relation family to two quoted types. -/
def sourceRelationApplication {calculus : ObjectCalculusExtension}
    (quotation : Quotation calculus) (source : Annotation) (level : Nat)
    (left right : Term n) : Term n :=
  .app (.app (quotation.relationFamily source level) left) right

/-- Every admissible quotation satisfies the typing and projection clauses of its universe equation. -/
def SatisfiesUniverseEquation {calculus : ObjectCalculusExtension}
    (quotation : Quotation calculus) (source target : Annotation) (level : Nat) : Prop :=
  calculus.hasType .empty (quotation.universeWitness source target level)
      (universeWitnessType quotation.relationFamily source target level) ∧
    calculus.convertible (quotation.projectedRelation (n := 0) source target level)
      (quotation.relationFamily (n := 0) source level)

/-- Admissibility derives the complete quoted structured-universe equation. -/
theorem satisfiesUniverseEquation {calculus : ObjectCalculusExtension}
    (quotation : Quotation calculus) {source target : Annotation} {level : Nat}
    (admissible : AdmissibleUniverseTranslation source target) :
    quotation.SatisfiesUniverseEquation source target level :=
  ⟨quotation.universeWitness_hasType source target level admissible,
    quotation.relationProjection_beta source target level admissible⟩

/-- Projection conversion remains valid after applying the relation to two terms. -/
theorem projectedRelationApplication_convertible {calculus : ObjectCalculusExtension}
    (quotation : Quotation calculus) {source target : Annotation} {level : Nat}
    (admissible : AdmissibleUniverseTranslation source target) (left right : Term n) :
    calculus.convertible
      (quotation.projectedRelationApplication source target level left right)
      (quotation.sourceRelationApplication source level left right) := by
  exact calculus.appFunction
    (calculus.appFunction
      (quotation.relationProjection_beta source target level admissible))

end Quotation

/-- Realizability of every quoted structured-universe witness in the unextended annotated calculus. -/
def CoreQuotationRealizability : Prop :=
  Nonempty (Quotation ObjectCalculusExtension.core)

/-- Alignment of quoted universe witnesses with synthesis realizers and abstraction relation types. -/
structure TranslationAlignment {calculus : ObjectCalculusExtension}
    (quotation : Quotation calculus)
    (realizers : AnnotatedRelationTranslation.SyntaxRealizers)
    (bridge : AnnotatedRelationTranslation.WitnessTypingBridge) where
  /-- The universe-rule realizer is the corresponding quoted universe witness. -/
  universeRule_eq : ∀ {n : Nat} (source target : Annotation) (level : Nat),
    AdmissibleUniverseTranslation source target →
      realizers.universeRule (n := n) source target level =
        quotation.universeWitness source target level
  /-- The abstraction bridge exposes application of the quoted projected relation. -/
  relationType_eq : ∀ {n : Nat} (source target : Annotation) (level : Nat),
    AdmissibleUniverseTranslation source target →
      ∀ left right : Term (AnnotatedRelationTranslation.relationalScope n),
        bridge.relationType (realizers.universeRule source target level) left right =
          quotation.projectedRelationApplication source target level left right

/-- The typing and projection facts inferred for a translated universe inhabitant. -/
def TranslatedTypeWitnessConclusion {calculus : ObjectCalculusExtension}
    (quotation : Quotation calculus)
    (bridge : AnnotatedRelationTranslation.WitnessTypingBridge)
    (context : AnnotatedRelationTranslation.Context n)
    (source target : Annotation) (level : Nat) (type type' : Term n)
    (typeWitness : Term (AnnotatedRelationTranslation.relationalScope n)) : Prop :=
  calculus.hasType context.gamma type' (.sort level source) ∧
    calculus.hasType (bridge.relationalContext context) typeWitness
      (quotation.projectedRelationApplication source target level
        (AnnotatedRelationTranslation.Term.original type)
        (AnnotatedRelationTranslation.Term.primed type')) ∧
    calculus.convertible
      (quotation.projectedRelationApplication source target level
        (AnnotatedRelationTranslation.Term.original type)
        (AnnotatedRelationTranslation.Term.primed type'))
      (quotation.sourceRelationApplication source level
        (AnnotatedRelationTranslation.Term.original type)
        (AnnotatedRelationTranslation.Term.primed type'))

/-- Abstraction plus quotation alignment derives translated type-witness typing and projection. -/
theorem translatedTypeWitnessConclusion_of_abstraction
    {calculus : ObjectCalculusExtension} {quotation : Quotation calculus}
    {realizers : AnnotatedRelationTranslation.SyntaxRealizers}
    {bridge : AnnotatedRelationTranslation.WitnessTypingBridge}
    (alignment : TranslationAlignment quotation realizers bridge)
    (abstraction : AnnotatedRelationTranslation.AbstractionClaim realizers bridge)
    {context : AnnotatedRelationTranslation.Context n} {source target : Annotation}
    {level : Nat} {type type' : Term n}
    {typeWitness : Term (AnnotatedRelationTranslation.relationalScope n)}
    (contextWellFormed : AnnotatedDependentCalculus.WellFormed context.gamma)
    (typeWellTyped : AnnotatedDependentCalculus.HasType context.gamma type (.sort level source))
    (typeTranslation : AnnotatedRelationTranslation.Judgment realizers context type
      (.sort level source) type' typeWitness)
    (admissible : AdmissibleUniverseTranslation source target) :
    TranslatedTypeWitnessConclusion quotation bridge context source target level type type'
      typeWitness := by
  have conclusion := abstraction contextWellFormed typeWellTyped typeTranslation
    (AnnotatedRelationTranslation.Judgment.sort admissible level)
  refine ⟨calculus.ofHasType conclusion.1, ?_⟩
  refine ⟨?_, quotation.projectedRelationApplication_convertible admissible _ _⟩
  apply calculus.ofHasType
  rw [← alignment.relationType_eq source target level admissible]
  exact conclusion.2

example {calculus : ObjectCalculusExtension} (quotation : Quotation calculus)
    {source target : Annotation} {level : Nat}
    (admissible : AdmissibleUniverseTranslation source target) :
    quotation.SatisfiesUniverseEquation source target level :=
  quotation.satisfiesUniverseEquation admissible

example : Prop := CoreQuotationRealizability

example {source target : Annotation}
    (assumptions : UniverseRelationAssumptions source target) :
    StructuredRelation target (Type) (Type) :=
  universeStructuredRelation source target assumptions

end DeepWiki.Refine.StructuredUniverseQuotation
