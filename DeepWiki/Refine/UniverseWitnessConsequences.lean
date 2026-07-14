import DeepWiki.Refine.AnnotatedRelationTranslation
import DeepWiki.Refine.UniverseRelationStructure

/-! # Consequences of annotated proof transfer

The abstraction claim types translated relation witnesses once the object language can quote
relation-record application. At the semantic level, every admissible universe-annotation pair
has the expected structured-relation family under branch-local univalence assumptions.
-/

namespace DeepWiki.Refine.UniverseWitnessConsequences

universe u

/-- Object-language syntax for applying the relation projection of a witness to two terms. -/
structure RelationProjectionSyntax where
  /-- Quote `rel(relationWitness) left right` in the relational scope. -/
  relationApplication : {n : Nat} →
    AnnotatedRelationTranslation.Term (AnnotatedRelationTranslation.relationalScope n) →
      AnnotatedRelationTranslation.Term (AnnotatedRelationTranslation.relationalScope n) →
        AnnotatedRelationTranslation.Term (AnnotatedRelationTranslation.relationalScope n) →
          AnnotatedRelationTranslation.Term (AnnotatedRelationTranslation.relationalScope n)

/-- A witness-typing bridge is lawful for universe witnesses when its relation type is their quoted projection. -/
structure LawfulUniverseWitnessBridge (bridge : AnnotatedRelationTranslation.WitnessTypingBridge)
    (realizers : AnnotatedRelationTranslation.SyntaxRealizers) (projection : RelationProjectionSyntax) where
  /-- The bridge type agrees with `rel(p□) A A'` for every indexed universe witness. -/
  relationType_universe : ∀ {n : Nat} (source target : Annotation) (level : Nat)
    (type type' : AnnotatedRelationTranslation.Term n),
    bridge.relationType (realizers.universeRule source target level)
      type.original type'.primed =
    projection.relationApplication (realizers.universeRule source target level)
      type.original type'.primed

/-- The relation-witness typing conclusion obtained from translating a universe-typed term. -/
def UniverseRelationWitnessTyping (bridge : AnnotatedRelationTranslation.WitnessTypingBridge)
    (realizers : AnnotatedRelationTranslation.SyntaxRealizers) (projection : RelationProjectionSyntax)
    (context : AnnotatedRelationTranslation.Context n) (source target : Annotation) (level : Nat)
    (type type' : AnnotatedRelationTranslation.Term n)
    (typeWitness : AnnotatedRelationTranslation.Term (AnnotatedRelationTranslation.relationalScope n)) : Prop :=
  AnnotatedDependentCalculus.HasType context.gamma type' (.sort level source) ∧
    AnnotatedDependentCalculus.HasType (bridge.relationalContext context) typeWitness
      (projection.relationApplication (realizers.universeRule source target level)
        type.original type'.primed)

/-- Abstraction and a lawful relation quote derive the universe relation-witness typing rule. -/
theorem universeRelationWitnessTyping_of_abstraction
    {bridge : AnnotatedRelationTranslation.WitnessTypingBridge}
    {realizers : AnnotatedRelationTranslation.SyntaxRealizers} {projection : RelationProjectionSyntax}
    (lawful : LawfulUniverseWitnessBridge bridge realizers projection)
    (abstraction : AnnotatedRelationTranslation.AbstractionClaim realizers bridge)
    {context : AnnotatedRelationTranslation.Context n} {source target : Annotation} {level : Nat}
    {type type' : AnnotatedRelationTranslation.Term n}
    {typeWitness : AnnotatedRelationTranslation.Term (AnnotatedRelationTranslation.relationalScope n)}
    (contextWellFormed : AnnotatedDependentCalculus.WellFormed context.gamma)
    (typeWellTyped :
      AnnotatedDependentCalculus.HasType context.gamma type (.sort level source))
    (typeTranslation :
      AnnotatedRelationTranslation.Judgment realizers context type (.sort level source) type' typeWitness)
    (admissible : AdmissibleUniverseTranslation source target) :
    UniverseRelationWitnessTyping bridge realizers projection context source target level
      type type' typeWitness := by
  have conclusion := abstraction contextWellFormed typeWellTyped typeTranslation
    (AnnotatedRelationTranslation.Judgment.sort admissible level)
  refine ⟨conclusion.1, ?_⟩
  rw [← lawful.relationType_universe]
  exact conclusion.2

/-- Branch-local assumptions can be recovered from annotation admissibility and conditional univalence. -/
def universeAssumptionsOfAdmissible (source target : Annotation)
    (admissible : AdmissibleUniverseTranslation source target)
    (univalentWhenNeeded : ¬ target.IsUniverseWeak → IsUnivalentUniverse.{u}) :
    UniverseRelationAssumptions.{u} source target := by
  by_cases targetWeak : target.IsUniverseWeak
  · exact .weak targetWeak
  · have sourceTop : source = Annotation.equivalence :=
      admissible.resolve_right targetWeak
    subst source
    exact .strong targetWeak (univalentWhenNeeded targetWeak)

/-- Every admissible universe pair has a semantic witness under only its non-weak univalence requirement. -/
def semanticUniverseWitnessOfAdmissible (source target : Annotation)
    (admissible : AdmissibleUniverseTranslation source target)
    (univalentWhenNeeded : ¬ target.IsUniverseWeak → IsUnivalentUniverse.{u}) :
    StructuredRelation.{u + 1, u + 1, u + 1} target (Type u) (Type u) :=
  universeStructuredRelation source target
    (universeAssumptionsOfAdmissible source target admissible univalentWhenNeeded)

/-- The semantic witness for an admissible universe pair relates types by source-structured relations. -/
@[simp] theorem semanticUniverseWitnessOfAdmissible_rel (source target : Annotation)
    (admissible : AdmissibleUniverseTranslation source target)
    (univalentWhenNeeded : ¬ target.IsUniverseWeak → IsUnivalentUniverse.{u}) :
    (semanticUniverseWitnessOfAdmissible source target admissible
      univalentWhenNeeded).rel =
      (fun A B : Type u => StructuredRelation.{u, u, u} source A B) :=
  universeStructuredRelation_rel source target
    (universeAssumptionsOfAdmissible source target admissible univalentWhenNeeded)

/-- A weak target constructs the semantic universe witness without univalence evidence. -/
def semanticUniverseWitnessOfWeak (source target : Annotation)
    (targetWeak : target.IsUniverseWeak) :
    StructuredRelation.{u + 1, u + 1, u + 1} target (Type u) (Type u) :=
  semanticUniverseWitnessOfAdmissible source target
    (admissibleUniverseTranslation_of_weak targetWeak)
    (fun targetNotWeak => (targetNotWeak targetWeak).elim)

/-- A non-weak target with top source constructs its semantic universe witness from explicit univalence. -/
def semanticUniverseWitnessOfTop (target : Annotation)
    (targetNotWeak : ¬ target.IsUniverseWeak) (univalent : IsUnivalentUniverse.{u}) :
    StructuredRelation.{u + 1, u + 1, u + 1} target (Type u) (Type u) :=
  universeStructuredRelation Annotation.equivalence target
    (.strong targetNotWeak univalent)

example {bridge : AnnotatedRelationTranslation.WitnessTypingBridge}
    {realizers : AnnotatedRelationTranslation.SyntaxRealizers} {projection : RelationProjectionSyntax}
    (lawful : LawfulUniverseWitnessBridge bridge realizers projection)
    (abstraction : AnnotatedRelationTranslation.AbstractionClaim realizers bridge)
    {context : AnnotatedRelationTranslation.Context n} {source target : Annotation} {level : Nat}
    {type type' : AnnotatedRelationTranslation.Term n}
    {typeWitness : AnnotatedRelationTranslation.Term (AnnotatedRelationTranslation.relationalScope n)}
    (contextWellFormed : AnnotatedDependentCalculus.WellFormed context.gamma)
    (typeWellTyped :
      AnnotatedDependentCalculus.HasType context.gamma type (.sort level source))
    (typeTranslation :
      AnnotatedRelationTranslation.Judgment realizers context type (.sort level source) type' typeWitness)
    (admissible : AdmissibleUniverseTranslation source target) :
    UniverseRelationWitnessTyping bridge realizers projection context source target level
      type type' typeWitness :=
  universeRelationWitnessTyping_of_abstraction lawful abstraction contextWellFormed typeWellTyped
    typeTranslation admissible

example (source target : Annotation) (targetWeak : target.IsUniverseWeak) :
    StructuredRelation.{u + 1, u + 1, u + 1} target (Type u) (Type u) :=
  semanticUniverseWitnessOfWeak source target targetWeak

example (target : Annotation) (targetNotWeak : ¬ target.IsUniverseWeak)
    (univalent : IsUnivalentUniverse.{u}) :
    StructuredRelation.{u + 1, u + 1, u + 1} target (Type u) (Type u) :=
  semanticUniverseWitnessOfTop target targetNotWeak univalent

example (source target : Annotation)
    (admissible : AdmissibleUniverseTranslation source target)
    (univalentWhenNeeded : ¬ target.IsUniverseWeak → IsUnivalentUniverse.{u}) :
    (semanticUniverseWitnessOfAdmissible source target admissible
      univalentWhenNeeded).rel =
      (fun A B : Type u => StructuredRelation.{u, u, u} source A B) :=
  semanticUniverseWitnessOfAdmissible_rel source target admissible univalentWhenNeeded

end DeepWiki.Refine.UniverseWitnessConsequences
