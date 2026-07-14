import DeepWiki.Refine.AnnotatedRelationTranslation

/-! # Canonical erasure of annotated synthesis

For the canonical self-translation context represented here, erasing a synthesis derivation
identifies the primed term with the source and the witness with raw translation. This normalization
is distinct from a general erasure into a raw parametricity sequent.
-/

namespace DeepWiki.Refine.AnnotatedTranslationErasure

open AnnotatedRelationTranslation

/-- Canonical-erasure laws required of fixed annotated object-language realizers. -/
structure CanonicalErasureLaws (realizers : SyntaxRealizers) : Prop where
  /-- Universe realizers erase to the raw relation between two universes. -/
  universeRuleErases : ∀ {n : Nat} (source target : Annotation) (level : Nat),
    (realizers.universeRule (n := n) source target level).erase =
      DependentCalculus.RawParametricity.translate (.sort level)
  /-- Arrow realizers erase to raw translation of the corresponding non-dependent product. -/
  arrowRuleErases : ∀ {n : Nat} (output : Annotation)
      (domain domain' codomain codomain' : AnnotatedDependentCalculus.Term n)
      (domainWitness codomainWitness :
        AnnotatedDependentCalculus.Term
          (DependentCalculus.RawParametricity.scopeSize n)),
    domain'.erase = domain.erase →
    codomain'.erase = codomain.erase →
    domainWitness.erase = DependentCalculus.RawParametricity.translate domain.erase →
    codomainWitness.erase = DependentCalculus.RawParametricity.translate codomain.erase →
    (realizers.arrow output domain domain' codomain codomain'
      domainWitness codomainWitness).erase =
        DependentCalculus.RawParametricity.translate
          (.pi domain.erase (codomain.erase.rename DependentCalculus.Renaming.shift))
  /-- Dependent-product realizers erase to raw dependent-product translation. -/
  piRuleErases : ∀ {n : Nat} (output : Annotation)
      (domain domain' : AnnotatedDependentCalculus.Term n)
      (codomain codomain' : AnnotatedDependentCalculus.Term (n + 1))
      (domainWitness : AnnotatedDependentCalculus.Term
        (DependentCalculus.RawParametricity.scopeSize n))
      (codomainWitness : AnnotatedDependentCalculus.Term
        (DependentCalculus.RawParametricity.scopeSize n + 3)),
    domain'.erase = domain.erase →
    codomain'.erase = codomain.erase →
    domainWitness.erase = DependentCalculus.RawParametricity.translate domain.erase →
    codomainWitness.erase = DependentCalculus.RawParametricity.translate codomain.erase →
    (realizers.pi output domain domain' codomain codomain'
      domainWitness codomainWitness).erase =
        DependentCalculus.RawParametricity.translate (.pi domain.erase codomain.erase)
  /-- Weakening annotation structure erases to the unchanged raw witness. -/
  weakeningErases : ∀ {n : Nat} (context : AnnotatedRelationTranslation.Context n)
      {source target : AnnotatedDependentCalculus.Term n}
      (subtype : AnnotatedDependentCalculus.Subtype context.gamma source target)
      (witness : AnnotatedDependentCalculus.Term
        (DependentCalculus.RawParametricity.scopeSize n)),
    (realizers.weakening context subtype witness).erase = witness.erase

/-- Membership in a translation context exposes the unique canonical entry at some source index. -/
theorem Context.exists_entryAt_of_contains
    {context : AnnotatedRelationTranslation.Context n}
    {entry : AnnotatedRelationTranslation.Context.Entry n}
    (member : context.Contains entry) :
    ∃ index, context.entryAt index = entry := by
  simpa only [AnnotatedRelationTranslation.Context.Contains,
    AnnotatedRelationTranslation.Context.entries, List.mem_ofFn] using member

/-- Canonical self-translation erases to the source term and its raw witness translation. -/
theorem Judgment.canonicalErasure {realizers : SyntaxRealizers}
    (laws : CanonicalErasureLaws realizers)
    {context : AnnotatedRelationTranslation.Context n}
    {term type term' : AnnotatedDependentCalculus.Term n}
    {witness : AnnotatedDependentCalculus.Term
      (DependentCalculus.RawParametricity.scopeSize n)}
    (translation : Judgment realizers context term type term' witness) :
    term'.erase = term.erase ∧
      witness.erase = DependentCalculus.RawParametricity.translate term.erase := by
  induction translation with
  | sort admissible level =>
      exact ⟨rfl, laws.universeRuleErases _ _ level⟩
  | @var _ context entry member contextWellFormed =>
      obtain ⟨index, rfl⟩ := Context.exists_entryAt_of_contains member
      exact ⟨rfl, by
        change (.var (DependentCalculus.RawParametricity.witnessRenaming _ index) :
          DependentCalculus.Term _) = _
        simp only [AnnotatedRelationTranslation.Context.entryAt,
          AnnotatedDependentCalculus.Term.erase,
          DependentCalculus.RawParametricity.translate_var]⟩
  | app functionTranslation argumentTranslation functionInduction argumentInduction =>
      refine ⟨?_, ?_⟩
      · simp only [AnnotatedDependentCalculus.Term.erase,
          functionInduction.1, argumentInduction.1]
      · simp only [AnnotatedRelationTranslation.Term.applyWitness,
          AnnotatedDependentCalculus.Term.erase,
          AnnotatedRelationTranslation.Term.original,
          AnnotatedRelationTranslation.Term.primed,
          AnnotatedDependentCalculus.Term.erase_rename,
          DependentCalculus.RawParametricity.original,
          DependentCalculus.RawParametricity.primed,
          argumentInduction.1,
          functionInduction.2, argumentInduction.2,
          DependentCalculus.RawParametricity.translate]
  | @lam n context domain domain' body codomain body' level annotation
      domainWitness bodyWitness domainTranslation bodyTranslation
      domainInduction bodyInduction =>
      refine ⟨?_, ?_⟩
      · simp only [AnnotatedDependentCalculus.Term.erase,
          domainInduction.1, bodyInduction.1]
      · have bodyWitnessErases :
            (bodyWitness.erase : DependentCalculus.Term
              (DependentCalculus.RawParametricity.scopeSize _ + 3)) =
              DependentCalculus.RawParametricity.translate body.erase :=
          bodyInduction.2
        rw [AnnotatedRelationTranslation.Term.erase_lambdaWitness]
        rw [bodyWitnessErases]
        simp only [AnnotatedRelationTranslation.Term.erase_original,
          AnnotatedRelationTranslation.Term.erase_primed,
          AnnotatedRelationTranslation.Term.erase_relatedDomain,
          AnnotatedDependentCalculus.Term.erase,
          domainInduction.1, domainInduction.2,
          DependentCalculus.RawParametricity.translate,
          DependentCalculus.ParametricitySequents.lambdaWitness,
          DependentCalculus.ParametricitySequents.relatedDomain]
  | arrow requirements domainTranslation codomainTranslation
      domainInduction codomainInduction =>
      refine ⟨by simp only [AnnotatedRelationTranslation.Term.arrow,
          AnnotatedDependentCalculus.Term.erase_arrow,
          domainInduction.1, codomainInduction.1], ?_⟩
      rw [AnnotatedRelationTranslation.Term.arrow,
        AnnotatedDependentCalculus.Term.erase_arrow]
      exact laws.arrowRuleErases _ _ _ _ _ _ _ domainInduction.1 codomainInduction.1
        domainInduction.2 codomainInduction.2
  | pi requirements domainTranslation codomainTranslation
      domainInduction codomainInduction =>
      exact ⟨by simp only [AnnotatedDependentCalculus.Term.erase,
          domainInduction.1, codomainInduction.1],
        laws.piRuleErases _ _ _ _ _ _ _ domainInduction.1 codomainInduction.1
          domainInduction.2 codomainInduction.2⟩
  | conversion translation subtype inductionHypothesis =>
      exact ⟨inductionHypothesis.1,
        (laws.weakeningErases _ subtype _).trans inductionHypothesis.2⟩

/-- Canonical-erasure normalization as a proposition for fixed lawful syntax realizers. -/
def CanonicalErasureClaim (realizers : SyntaxRealizers) : Prop :=
  CanonicalErasureLaws realizers →
    ∀ {n : Nat} {context : AnnotatedRelationTranslation.Context n}
      {term type term' : AnnotatedDependentCalculus.Term n}
      {witness : AnnotatedDependentCalculus.Term
        (DependentCalculus.RawParametricity.scopeSize n)},
      Judgment realizers context term type term' witness →
        term'.erase = term.erase ∧
          witness.erase = DependentCalculus.RawParametricity.translate term.erase

/-- Lawful syntax realizers satisfy canonical-erasure normalization. -/
theorem canonicalErasureClaim (realizers : SyntaxRealizers) :
    CanonicalErasureClaim realizers :=
  by
    intro laws n context term type term' witness translation
    exact Judgment.canonicalErasure laws translation

example (realizers : SyntaxRealizers) : CanonicalErasureClaim realizers :=
  canonicalErasureClaim realizers

end DeepWiki.Refine.AnnotatedTranslationErasure
