import DeepWiki.Refine.AnnotatedParametricityErasure
import DeepWiki.Refine.MaximalAnnotation
import DeepWiki.Refine.ParametricitySequentRenaming
import DeepWiki.Refine.StructuredUniverseQuotationSyntax

/-! # Structural realizers for annotated-parametricity erasure

Maximal annotation embeds raw parametricity witnesses back into annotated syntax and supplies an
erasure-only structural model without a primitive relation-field projection.
-/

namespace DeepWiki.Refine.AnnotatedParametricityErasureRealizers

open AnnotatedParametricityErasure
open DependentCalculus
open DependentCalculus.RawParametricity
open DependentCalculus.ParametricitySequents

/-- A raw relational lambda with an arbitrary witness-domain type is natural under renaming. -/
theorem rawLambdaWitness_rename
    (domain primedDomain : Term source) (witnessDomain : Term (source + 2))
    (bodyRelation : Term (source + 3)) (mapping : Renaming source target) :
    (lambdaWitness domain primedDomain witnessDomain bodyRelation).rename mapping =
      lambdaWitness (domain.rename mapping) (primedDomain.rename mapping)
        (witnessDomain.rename (liftBy mapping 2))
        (bodyRelation.rename (liftTripleRenaming mapping)) := by
  unfold lambdaWitness
  simp only [Term.rename, weakenBy_rename]
  rw [liftTripleRenaming_eq_liftBy]
  rfl

/-- Lifting beneath one binder preserves injectivity of a variable renaming. -/
theorem renamingLift_injective (mapping : Renaming source target)
    (injective : Function.Injective mapping) :
    Function.Injective (Renaming.lift mapping) := by
  intro left right equal
  cases left using Fin.cases with
  | zero =>
      cases right using Fin.cases with
      | zero => rfl
      | succ right =>
          have valuesEqual := congrArg Fin.val equal
          simp only [Renaming.lift_zero, Renaming.lift_succ,
            Fin.val_zero, Fin.val_succ] at valuesEqual
          omega
  | succ left =>
      cases right using Fin.cases with
      | zero =>
          have valuesEqual := congrArg Fin.val equal
          simp only [Renaming.lift_zero, Renaming.lift_succ,
            Fin.val_zero, Fin.val_succ] at valuesEqual
          omega
      | succ right =>
          congr 1
          apply injective
          apply Fin.ext
          have valuesEqual := congrArg Fin.val equal
          simp only [Renaming.lift_succ, Fin.val_succ] at valuesEqual
          omega

/-- Lifting beneath finitely many binders preserves injectivity. -/
theorem liftBy_injective (mapping : Renaming source target)
    (injective : Function.Injective mapping) :
    ∀ amount, Function.Injective (liftBy mapping amount)
  | 0 => injective
  | amount + 1 => renamingLift_injective _ (liftBy_injective mapping injective amount)

/-- Triple lifting preserves injectivity of a scoped variable renaming. -/
theorem liftTripleRenaming_injective (mapping : Renaming source target)
    (injective : Function.Injective mapping) :
    Function.Injective (liftTripleRenaming mapping) := by
  rw [liftTripleRenaming_eq_liftBy]
  exact liftBy_injective mapping injective 3

/-- The closed raw universe relation is invariant under ambient renaming. -/
theorem sortRelation_rename (level : Nat) (mapping : Renaming source target) :
    (sortRelation level source).rename mapping = sortRelation level target := by
  have liftTwoOne :
      Renaming.lift (Renaming.lift mapping) (1 : Fin (source + 2)) =
        (1 : Fin (target + 2)) := by
    apply Fin.ext
    rfl
  have liftThreeOne :
      Renaming.lift (Renaming.lift (Renaming.lift mapping))
          (1 : Fin (source + 3)) =
        (1 : Fin (target + 3)) := by
    apply Fin.ext
    rfl
  unfold sortRelation
  simp only [Term.rename]
  rw [liftTwoOne, liftThreeOne]

/-- Shifting a term before lifting a renaming equals renaming before shifting. -/
theorem rename_shift_lift (term : Term source) (mapping : Renaming source target) :
    (term.rename Renaming.shift).rename (Renaming.lift mapping) =
      (term.rename mapping).rename Renaming.shift := by
  rw [Term.rename_comp, Term.rename_comp]
  apply Term.rename_congr
  funext index
  rfl

/-- Literal raw sequents are natural under injective renaming. -/
theorem rawSequentRenameInjective
    {context : ParametricityContext source} {term term' relation : Term source}
    (sequent : RawSequent context term term' relation)
    (contextWellFormed : context.WellFormed)
    (mapping : Renaming source target) (injective : Function.Injective mapping) :
    RawSequent (context.rename mapping)
      (term.rename mapping) (term'.rename mapping) (relation.rename mapping) := by
  induction sequent generalizing target with
  | paramSort caseContext level =>
      rw [sortRelation_rename]
      exact RawSequent.paramSort (caseContext.rename mapping) level
  | @paramVar _ caseContext _ triple member =>
      have renamedMember :
          VariableTriple.rename mapping triple ∈ caseContext.rename mapping :=
        List.mem_map.mpr ⟨triple, member, rfl⟩
      simpa only [Term.rename, VariableTriple.rename] using
        RawSequent.paramVar (contextWellFormed.rename mapping injective) renamedMember
  | paramApp _ _ functionInduction argumentInduction =>
      exact .paramApp
        (functionInduction contextWellFormed mapping injective)
        (argumentInduction contextWellFormed mapping injective)
  | @paramLam _ caseContext domain primedDomain witnessDomain body body' bodyRelation
      bodySequent bodyInduction =>
      have renamedBody := bodyInduction contextWellFormed.extend
        (liftTripleRenaming mapping) (liftTripleRenaming_injective mapping injective)
      rw [ParametricityContext.rename_extend,
        rename_originalBinderRenaming, rename_primedBinderRenaming] at renamedBody
      have result := RawSequent.paramLam
        (domain := domain.rename mapping)
        (primedDomain := primedDomain.rename mapping)
        (witnessDomain := witnessDomain.rename (liftBy mapping 2)) renamedBody
      simpa only [Term.rename,
        rawLambdaWitness_rename] using result
  | paramPi domainSequent codomainSequent domainInduction codomainInduction =>
      have renamedCodomain := codomainInduction contextWellFormed.extend
        (liftTripleRenaming mapping) (liftTripleRenaming_injective mapping injective)
      rw [ParametricityContext.rename_extend,
        rename_originalBinderRenaming, rename_primedBinderRenaming] at renamedCodomain
      have result := RawSequent.paramPi
        (domainInduction contextWellFormed mapping injective) renamedCodomain
      simpa only [Term.rename, piWitness_rename] using result

/-- Literal raw sequents are monotone in a well-formed variable-triple context. -/
theorem rawSequentChangeContext
    {context : ParametricityContext n} {term term' relation : Term n}
    (sequent : RawSequent context term term' relation)
    (target : ParametricityContext n) (targetWellFormed : target.WellFormed)
    (included : ∀ triple, triple ∈ context → triple ∈ target) :
    RawSequent target term term' relation := by
  induction sequent with
  | paramSort _ level => exact .paramSort target level
  | paramVar _ member => exact .paramVar targetWellFormed (included _ member)
  | paramApp _ _ functionInduction argumentInduction =>
      exact .paramApp (functionInduction target targetWellFormed included)
        (argumentInduction target targetWellFormed included)
  | paramLam bodySequent bodyInduction =>
      apply RawSequent.paramLam
      apply bodyInduction target.extend targetWellFormed.extend
      intro triple member
      simp only [ParametricityContext.extend, List.mem_cons, List.mem_map] at member ⊢
      rcases member with rfl | ⟨older, olderMember, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨older, included older olderMember, rfl⟩
  | paramPi domainSequent codomainSequent domainInduction codomainInduction =>
      apply RawSequent.paramPi
        (domainInduction target targetWellFormed included)
      apply codomainInduction target.extend targetWellFormed.extend
      intro triple member
      simp only [ParametricityContext.extend, List.mem_cons, List.mem_map] at member ⊢
      rcases member with rfl | ⟨older, olderMember, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨older, included older olderMember, rfl⟩

/-- A literal raw sequent weakens beneath one unrelated relational variable triple. -/
theorem rawSequentWeakenTriple
    {context : ParametricityContext n} {term term' relation : Term n}
    (sequent : RawSequent context term term' relation)
    (contextWellFormed : context.WellFormed) :
    RawSequent context.extend
      (term.rename ParametricityContext.shiftThree)
      (term'.rename ParametricityContext.shiftThree)
      (relation.rename ParametricityContext.shiftThree) := by
  have renamed := rawSequentRenameInjective sequent contextWellFormed
    ParametricityContext.shiftThree ParametricityContext.shiftThree_injective
  apply rawSequentChangeContext renamed context.extend contextWellFormed.extend
  intro triple member
  simp only [ParametricityContext.rename, ParametricityContext.extend,
    List.mem_cons, List.mem_map] at member ⊢
  obtain ⟨older, olderMember, rfl⟩ := member
  exact Or.inr ⟨older, olderMember, rfl⟩

/-- The original codomain copy before insertion of its relational binder triple. -/
def originalCodomain (codomain : AnnotatedDependentCalculus.Term (n + 1)) :
    Term (scopeSize n + 1) :=
  codomain.erase.rename (Renaming.lift (originalRenaming n))

/-- The primed codomain copy before insertion of its relational binder triple. -/
def primedCodomain (codomain : AnnotatedDependentCalculus.Term (n + 1)) :
    Term (scopeSize n + 1) :=
  codomain.erase.rename (Renaming.lift (primedRenaming n))

/-- The canonical raw relation witness for a non-dependent arrow. -/
def rawArrowWitness (domain domain' codomain codomain' : AnnotatedDependentCalculus.Term n)
    (domainWitness codomainWitness : AnnotatedDependentCalculus.Term (scopeSize n)) :
    Term (scopeSize n) :=
  piWitness
    (AnnotatedRelationTranslation.Term.original domain).erase
    ((AnnotatedRelationTranslation.Term.original codomain).erase.rename Renaming.shift)
    (AnnotatedRelationTranslation.Term.primed domain').erase
    ((AnnotatedRelationTranslation.Term.primed codomain').erase.rename Renaming.shift)
    domainWitness.erase
    (codomainWitness.erase.rename ParametricityContext.shiftThree)

/-- The canonical raw relation witness for a dependent product. -/
def rawPiWitness (domain domain' : AnnotatedDependentCalculus.Term n)
    (codomain codomain' : AnnotatedDependentCalculus.Term (n + 1))
    (domainWitness : AnnotatedDependentCalculus.Term (scopeSize n))
    (codomainWitness : AnnotatedDependentCalculus.Term (scopeSize n + 3)) :
    Term (scopeSize n) :=
  piWitness
    (AnnotatedRelationTranslation.Term.original domain).erase
    (originalCodomain codomain)
    (AnnotatedRelationTranslation.Term.primed domain').erase
    (primedCodomain codomain')
    domainWitness.erase codomainWitness.erase

/-- Maximal annotation of canonical raw witnesses realizes the erasure-only structural model. -/
def canonicalRawRealizers : AnnotatedRelationTranslation.SyntaxRealizers where
  universeRule := fun _ _ level =>
    MaximalAnnotation.Term.annotate (sortRelation level _)
  arrow := fun _ domain domain' codomain codomain' domainWitness codomainWitness =>
    MaximalAnnotation.Term.annotate
      (rawArrowWitness domain domain' codomain codomain' domainWitness codomainWitness)
  pi := fun _ domain domain' codomain codomain' domainWitness codomainWitness =>
    MaximalAnnotation.Term.annotate
      (rawPiWitness domain domain' codomain codomain' domainWitness codomainWitness)
  weakening := by
    intro n context source target subtype witness
    exact witness

/-- The maximally annotated raw realizers satisfy the complete erasure interface. -/
theorem canonicalRawRealizers_erasureLaws :
    ErasureLaws canonicalRawRealizers RelationFieldSyntax.erasure := by
  constructor
  · intro n term
    exact relationProjectionStar_erasure _
  · intro n term
    exact relationProjectionStar_erasure _
  · intro n index
    exact relationProjectionStar_erasure _
  · intro n source target level admissible
    simpa only [canonicalRawRealizers, relationProjectionStar_erasure] using
      MaximalAnnotation.Term.erase_annotate
        (sortRelation level (scopeSize n))
  · intro n context output domain domain' codomain codomain'
      domainWitness codomainWitness domainSequent codomainSequent
    rw [relationProjectionStar_erasure] at domainSequent codomainSequent ⊢
    have codomainWeakened := rawSequentWeakenTriple codomainSequent
      (eraseParametricityContext_wellFormed context)
    have originalBody :
        ((AnnotatedRelationTranslation.Term.original codomain).erase.rename
            Renaming.shift).rename originalBinderRenaming =
          (AnnotatedRelationTranslation.Term.original codomain).erase.rename
            ParametricityContext.shiftThree := by
      rw [Term.rename_comp]
      apply Term.rename_congr
      funext index
      rfl
    have primedBody :
        ((AnnotatedRelationTranslation.Term.primed codomain').erase.rename
            Renaming.shift).rename primedBinderRenaming =
          (AnnotatedRelationTranslation.Term.primed codomain').erase.rename
            ParametricityContext.shiftThree := by
      rw [Term.rename_comp]
      apply Term.rename_congr
      funext index
      rfl
    rw [← originalBody, ← primedBody] at codomainWeakened
    have result := RawSequent.paramPi domainSequent codomainWeakened
    simpa only [canonicalRawRealizers, MaximalAnnotation.Term.erase_annotate,
      rawArrowWitness, AnnotatedRelationTranslation.Term.arrow,
      AnnotatedDependentCalculus.Term.erase_arrow,
      AnnotatedRelationTranslation.Term.erase_original,
      AnnotatedRelationTranslation.Term.erase_primed,
      RawParametricity.original, RawParametricity.primed,
      Term.rename, rename_shift_lift] using result
  · intro n context output domain domain' codomain codomain'
      domainWitness codomainWitness domainSequent codomainSequent
    rw [relationProjectionStar_erasure] at domainSequent codomainSequent ⊢
    have normalizedCodomainSequent :
        RawSequent (eraseParametricityContext context).extend
          (RawParametricity.original codomain.erase)
          (RawParametricity.primed codomain'.erase) codomainWitness.erase := by
      simpa only [eraseParametricityContext_extend,
        AnnotatedRelationTranslation.Term.erase_original,
        AnnotatedRelationTranslation.Term.erase_primed,
        RawParametricity.scopeSize] using codomainSequent
    rw [← originalBody_underBinder codomain.erase,
      ← primedBody_underBinder codomain'.erase] at normalizedCodomainSequent
    have result := RawSequent.paramPi domainSequent normalizedCodomainSequent
    simpa only [canonicalRawRealizers, MaximalAnnotation.Term.erase_annotate,
      rawPiWitness, originalCodomain, primedCodomain,
      AnnotatedDependentCalculus.Term.erase,
      AnnotatedRelationTranslation.Term.erase_original,
      AnnotatedRelationTranslation.Term.erase_primed,
      RawParametricity.original, RawParametricity.primed,
      Term.rename] using result
  · intro n context source target subtype witness
    simp only [canonicalRawRealizers, relationProjectionStar_erasure]

example : ErasureLaws canonicalRawRealizers RelationFieldSyntax.erasure :=
  canonicalRawRealizers_erasureLaws

end DeepWiki.Refine.AnnotatedParametricityErasureRealizers

namespace DeepWiki.Refine.StructuredUniverseQuotationErasure

open StructuredUniverseQuotationSyntax
open AnnotatedParametricityErasureRealizers
open DependentCalculus

/-- Partially read the raw relation denoted by a genuine structured quotation head. -/
def rawRelationField? : StructuredUniverseQuotationSyntax.Term n →
    Option (DependentCalculus.Term n)
  | .relationFamily _ level =>
      some (DependentCalculus.RawParametricity.sortRelation level n)
  | .universeWitness _ _ level =>
      some (DependentCalculus.RawParametricity.sortRelation level n)
  | .relationProjection witness => rawRelationField? witness
  | _ => none

/-- A quoted relation family reads back as the raw relation at the same universe level. -/
@[simp] theorem rawRelationField?_relationFamily
    (annotation : Annotation) (level : Nat) :
    rawRelationField?
        (.relationFamily annotation level : StructuredUniverseQuotationSyntax.Term n) =
      some (DependentCalculus.RawParametricity.sortRelation level n) :=
  rfl

/-- A genuine quoted universe witness reads back through its relation field. -/
@[simp] theorem rawRelationField?_universeWitness
    (source target : Annotation) (level : Nat) :
    rawRelationField?
        (.universeWitness source target level : StructuredUniverseQuotationSyntax.Term n) =
      some (DependentCalculus.RawParametricity.sortRelation level n) :=
  rfl

/-- Relation-field projection preserves the partial raw relation reading. -/
@[simp] theorem rawRelationField?_relationProjection
    (witness : StructuredUniverseQuotationSyntax.Term n) :
    rawRelationField? (.relationProjection witness) = rawRelationField? witness :=
  rfl

/-- The genuine projected universe witness erases to the raw universe relation. -/
theorem projectedUniverseWitness_rawRelation
    (source target : Annotation) (level : Nat) :
    rawRelationField?
        (projectedRelation source target level :
          StructuredUniverseQuotationSyntax.Term n) =
      some (DependentCalculus.RawParametricity.sortRelation level n) :=
  rfl

/-- The genuine projection reduction preserves its raw relation interpretation. -/
theorem universeProjection_rawRelation
    (source target : Annotation) (level : Nat) :
    rawRelationField?
        (projectedRelation source target level :
          StructuredUniverseQuotationSyntax.Term n) =
      rawRelationField? (.relationFamily source level) :=
  rfl

/-- Genuine quotation and the erasure-only structural realizer agree on universe witnesses. -/
theorem genuineUniverseErasure_agrees_canonicalRawRealizers
    {n : Nat} (source target : Annotation) (level : Nat)
    (_admissible : AdmissibleUniverseTranslation source target) :
    rawRelationField?
        (RelationFieldQuotation.canonical.relationField target
          (.universeWitness source target level :
            StructuredUniverseQuotationSyntax.Term
              (DependentCalculus.RawParametricity.scopeSize n))) =
      some ((canonicalRawRealizers.universeRule
        (n := n) source target level).erase) := by
  simp only [RelationFieldQuotation.canonical,
    rawRelationField?_relationProjection, rawRelationField?_universeWitness,
    canonicalRawRealizers, MaximalAnnotation.Term.erase_annotate]

end DeepWiki.Refine.StructuredUniverseQuotationErasure
