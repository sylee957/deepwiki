import DeepWiki.Refine.MaximalAnnotation
import DeepWiki.Refine.AnnotatedParametricityErasure
import DeepWiki.Refine.UnivalentParametricitySequents

/-! # Maximal annotation scope bridge

Canonical three-copy univalent sequents align with maximal annotated synthesis under explicit
equations for the object-language realizers.
-/

namespace DeepWiki.Refine.MaximalAnnotation

namespace Context

/-- Turn an ordinary typing context into the source context of annotated synthesis. -/
def toTranslation : UnderlyingDependentCalculus.Context n →
    AnnotatedRelationTranslation.Context n
  | .empty => .empty
  | .extend context type => .extend (toTranslation context) (Term.annotate type)

/-- The source typing context of maximal synthesis is the maximally annotated context. -/
@[simp] theorem gamma_toTranslation (context : UnderlyingDependentCalculus.Context n) :
    (toTranslation context).gamma = annotate context := by
  induction context with
  | empty => rfl
  | extend context type inductionHypothesis =>
      simp only [toTranslation, AnnotatedRelationTranslation.Context.gamma_extend,
        annotate, inductionHypothesis]

/-- Maximal translation-context extension is definitionally componentwise. -/
@[simp] theorem toTranslation_extend (context : UnderlyingDependentCalculus.Context n)
    (type : UnderlyingDependentCalculus.Term n) :
    toTranslation (.extend context type) =
      .extend (toTranslation context) (Term.annotate type) :=
  rfl

/-- The canonical triple context with one relational triple per source variable. -/
def canonicalParametricityContext : (n : Nat) →
    DependentCalculus.ParametricitySequents.ParametricityContext
      (DependentCalculus.RawParametricity.scopeSize n)
  | 0 => []
  | n + 1 =>
      (canonicalParametricityContext n).extend

/-- Erasing a maximal synthesis context gives the canonical triple context. -/
@[simp] theorem eraseParametricityContext_toTranslation
    (context : UnderlyingDependentCalculus.Context n) :
    AnnotatedParametricityErasure.eraseParametricityContext (toTranslation context) =
      canonicalParametricityContext n := by
  induction context with
  | empty => rfl
  | extend context type inductionHypothesis =>
      simp only [toTranslation,
        AnnotatedParametricityErasure.eraseParametricityContext_extend,
        canonicalParametricityContext, inductionHypothesis]

/-- Every canonical source variable occurs in its maximal synthesis context. -/
theorem entryAt_contains (context : UnderlyingDependentCalculus.Context n)
    (index : Fin n) :
    (toTranslation context).Contains ((toTranslation context).entryAt index) := by
  change (toTranslation context).entryAt index ∈
    List.ofFn (toTranslation context).entryAt
  exact List.mem_ofFn.mpr ⟨index, rfl⟩


end Context

namespace Term

/-- Maximal annotation commutes with the original-copy relational embedding. -/
@[simp] theorem annotate_original (term : DependentCalculus.Term n) :
    annotate (DependentCalculus.RawParametricity.original term) =
      AnnotatedRelationTranslation.Term.original (annotate term) := by
  simpa only [DependentCalculus.RawParametricity.original,
    AnnotatedRelationTranslation.Term.original] using
      annotate_rename term (DependentCalculus.RawParametricity.originalRenaming n)

/-- Maximal annotation commutes with the primed-copy relational embedding. -/
@[simp] theorem annotate_primed (term : DependentCalculus.Term n) :
    annotate (DependentCalculus.RawParametricity.primed term) =
      AnnotatedRelationTranslation.Term.primed (annotate term) := by
  simpa only [DependentCalculus.RawParametricity.primed,
    AnnotatedRelationTranslation.Term.primed] using
      annotate_rename term (DependentCalculus.RawParametricity.primedRenaming n)

/-- Maximal annotation commutes with weakening by any number of binders. -/
@[simp] theorem annotate_weakenBy (term : DependentCalculus.Term n) (amount : Nat) :
    annotate (DependentCalculus.RawParametricity.weakenBy term amount) =
      AnnotatedRelationTranslation.Term.weakenBy (annotate term) amount := by
  induction amount with
  | zero => rfl
  | succ amount inductionHypothesis =>
      simp only [DependentCalculus.RawParametricity.weakenBy,
        AnnotatedRelationTranslation.Term.weakenBy, annotate_rename,
        inductionHypothesis]

/-- Maximal annotation commutes with the relation type of a binder triple. -/
@[simp] theorem annotate_relatedDomain
    (relation : DependentCalculus.Term
      (DependentCalculus.RawParametricity.scopeSize n)) :
    annotate (DependentCalculus.ParametricitySequents.relatedDomain relation) =
      AnnotatedRelationTranslation.Term.relatedDomain (annotate relation) := by
  simp only [DependentCalculus.ParametricitySequents.relatedDomain,
    AnnotatedRelationTranslation.Term.relatedDomain, annotate,
    annotate_weakenBy]

/-- Maximal annotation commutes with the three binders of a relational lambda. -/
@[simp] theorem annotate_lambdaWitness (domain domain' : DependentCalculus.Term n)
    (domainWitness : DependentCalculus.Term
      (DependentCalculus.RawParametricity.scopeSize n))
    (bodyWitness : DependentCalculus.Term
      (DependentCalculus.RawParametricity.scopeSize n + 3)) :
    annotate
        (DependentCalculus.ParametricitySequents.lambdaWitness
          (DependentCalculus.RawParametricity.original domain)
          (DependentCalculus.RawParametricity.primed domain')
          (DependentCalculus.ParametricitySequents.relatedDomain domainWitness)
          bodyWitness) =
      AnnotatedRelationTranslation.Term.lambdaWitness
        (annotate domain) (annotate domain') (annotate domainWitness)
        (annotate bodyWitness) := by
  simp only [DependentCalculus.ParametricitySequents.lambdaWitness,
    AnnotatedRelationTranslation.Term.lambdaWitness,
    annotate, annotate_original, annotate_primed,
    annotate_weakenBy, annotate_relatedDomain]

/-- Maximal annotation commutes with application of a relational function witness. -/
@[simp] theorem annotate_applyWitness
    (functionWitness : DependentCalculus.Term
      (DependentCalculus.RawParametricity.scopeSize n))
    (argument argument' : DependentCalculus.Term n)
    (argumentWitness : DependentCalculus.Term
      (DependentCalculus.RawParametricity.scopeSize n)) :
    annotate
        (.app (.app (.app functionWitness
          (DependentCalculus.RawParametricity.original argument))
          (DependentCalculus.RawParametricity.primed argument')) argumentWitness) =
      AnnotatedRelationTranslation.Term.applyWitness
        (annotate functionWitness) (annotate argument) (annotate argument')
        (annotate argumentWitness) := by
  simp only [AnnotatedRelationTranslation.Term.applyWitness,
    annotate, annotate_original, annotate_primed]

end Term

namespace ScopeBridge

/-- Lift an annotation-free subtype into the maximal synthesis source context. -/
theorem translatedSubtype {context : UnderlyingDependentCalculus.Context n}
    {source target : UnderlyingDependentCalculus.Term n}
    (subtype : UnderlyingDependentCalculus.Subtype context source target) :
    AnnotatedDependentCalculus.Subtype (Context.toTranslation context).gamma
      (Term.annotate source) (Term.annotate target) := by
  simpa only [Context.gamma_toTranslation] using subtypeDerivation subtype

/-- Equations identifying maximal annotated realizers with univalent-parametricity realizers. -/
structure RealizerAgreement
    (annotated : AnnotatedRelationTranslation.SyntaxRealizers)
    (univalent : DependentCalculus.UnivalentParametricitySequents.SyntaxRealizers) : Prop where
  /-- The maximal annotated universe rule is maximal annotation of the univalent rule. -/
  universeRuleAgreement : ∀ {n : Nat} (level : Nat),
    annotated.universeRule (n := n) Annotation.equivalence Annotation.equivalence level =
      Term.annotate
        (univalent.universeRelation level (DependentCalculus.RawParametricity.scopeSize n))
  /-- The maximal annotated product rule is maximal annotation of the univalent rule. -/
  productRuleAgreement : ∀ {n : Nat}
      (domain domain' : DependentCalculus.Term n)
      (codomain codomain' : DependentCalculus.Term (n + 1))
      (domainWitness : DependentCalculus.Term
        (DependentCalculus.RawParametricity.scopeSize n))
      (codomainWitness : DependentCalculus.Term
        (DependentCalculus.RawParametricity.scopeSize n + 3)),
    annotated.pi Annotation.equivalence
        (Term.annotate domain) (Term.annotate domain')
        (Term.annotate codomain) (Term.annotate codomain')
        (Term.annotate domainWitness) (Term.annotate codomainWitness) =
      Term.annotate (univalent.dependentProduct domainWitness codomainWitness)
  /-- Maximal weakening along a lifted subtype leaves a maximally annotated witness unchanged. -/
  weakeningAgreement : ∀ {n : Nat}
      {context : UnderlyingDependentCalculus.Context n}
      {source target : UnderlyingDependentCalculus.Term n}
      (subtype : UnderlyingDependentCalculus.Subtype context source target)
      (witness : DependentCalculus.Term
        (DependentCalculus.RawParametricity.scopeSize n)),
    annotated.weakening (Context.toTranslation context)
        (translatedSubtype subtype) (Term.annotate witness) =
      Term.annotate witness

/-- Canonical univalent and maximal annotated derivations for the same scoped translation. -/
def MaximalCorrespondence
    (annotated : AnnotatedRelationTranslation.SyntaxRealizers)
    (univalent : DependentCalculus.UnivalentParametricitySequents.SyntaxRealizers)
    (context : UnderlyingDependentCalculus.Context n)
    (term type term' : UnderlyingDependentCalculus.Term n)
    (witness : DependentCalculus.Term
      (DependentCalculus.RawParametricity.scopeSize n)) : Prop :=
  DependentCalculus.UnivalentParametricitySequents.Sequent univalent
      (AnnotatedParametricityErasure.eraseParametricityContext
        (Context.toTranslation context))
      (DependentCalculus.RawParametricity.original term)
      (DependentCalculus.RawParametricity.primed term') witness ∧
    AnnotatedRelationTranslation.Judgment annotated (Context.toTranslation context)
      (Term.annotate term) (Term.annotate type) (Term.annotate term')
      (Term.annotate witness)

/-- The canonical correspondence contains its univalent-parametricity sequent. -/
theorem MaximalCorrespondence.univalent
    {annotated : AnnotatedRelationTranslation.SyntaxRealizers}
    {univalent : DependentCalculus.UnivalentParametricitySequents.SyntaxRealizers}
    {context : UnderlyingDependentCalculus.Context n}
    {term type term' : UnderlyingDependentCalculus.Term n}
    {witness : DependentCalculus.Term
      (DependentCalculus.RawParametricity.scopeSize n)}
    (correspondence :
      MaximalCorrespondence annotated univalent context term type term' witness) :
    DependentCalculus.UnivalentParametricitySequents.Sequent univalent
      (AnnotatedParametricityErasure.eraseParametricityContext
        (Context.toTranslation context))
      (DependentCalculus.RawParametricity.original term)
      (DependentCalculus.RawParametricity.primed term') witness :=
  correspondence.1

/-- The canonical correspondence contains its maximal annotated synthesis derivation. -/
theorem MaximalCorrespondence.annotated
    {annotated : AnnotatedRelationTranslation.SyntaxRealizers}
    {univalent : DependentCalculus.UnivalentParametricitySequents.SyntaxRealizers}
    {context : UnderlyingDependentCalculus.Context n}
    {term type term' : UnderlyingDependentCalculus.Term n}
    {witness : DependentCalculus.Term
      (DependentCalculus.RawParametricity.scopeSize n)}
    (correspondence :
      MaximalCorrespondence annotated univalent context term type term' witness) :
    AnnotatedRelationTranslation.Judgment annotated (Context.toTranslation context)
      (Term.annotate term) (Term.annotate type) (Term.annotate term')
      (Term.annotate witness) :=
  correspondence.2

/-- Universe translation satisfies the canonical maximal correspondence. -/
theorem maximalCorrespondence_sort
    {annotated : AnnotatedRelationTranslation.SyntaxRealizers}
    {univalent : DependentCalculus.UnivalentParametricitySequents.SyntaxRealizers}
    (agreement : RealizerAgreement annotated univalent)
    (context : UnderlyingDependentCalculus.Context n) (level : Nat) :
    MaximalCorrespondence annotated univalent context (.sort level) (.sort (level + 1))
      (.sort level)
      (univalent.universeRelation level
        (DependentCalculus.RawParametricity.scopeSize n)) := by
  constructor
  · exact .sort _ level
  · rw [← agreement.universeRuleAgreement level]
    exact AnnotatedRelationTranslation.Judgment.sort
      (admissibleUniverseTranslation_of_equivalence Annotation.equivalence) level

/-- A canonical source variable satisfies the maximal correspondence. -/
theorem maximalCorrespondence_var
    {annotated : AnnotatedRelationTranslation.SyntaxRealizers}
    {univalent : DependentCalculus.UnivalentParametricitySequents.SyntaxRealizers}
    {context : UnderlyingDependentCalculus.Context n}
    (contextWellFormed : UnderlyingDependentCalculus.WellFormed context)
    (index : Fin n) :
    MaximalCorrespondence annotated univalent context (.var index)
      (context.lookup index) (.var index)
      (.var (DependentCalculus.RawParametricity.witnessRenaming n index)) := by
  constructor
  · simpa only [DependentCalculus.RawParametricity.original_var,
      DependentCalculus.RawParametricity.primed_var,
      AnnotatedParametricityErasure.rawTriple] using
        DependentCalculus.UnivalentParametricitySequents.Sequent.var
          (AnnotatedParametricityErasure.eraseParametricityContext_wellFormed
            (Context.toTranslation context))
          (AnnotatedParametricityErasure.rawTriple_mem
            (Context.toTranslation context) index)
  · have annotatedWellFormed :
        AnnotatedDependentCalculus.WellFormed (Context.toTranslation context).gamma := by
      simpa only [Context.gamma_toTranslation] using wellFormed contextWellFormed
    simpa only [AnnotatedRelationTranslation.Context.entryAt,
      Context.gamma_toTranslation, ← Context.annotate_lookup, Term.annotate] using
        AnnotatedRelationTranslation.Judgment.var
          (Context.entryAt_contains context index) annotatedWellFormed

/-- Application preserves the canonical maximal correspondence. -/
theorem maximalCorrespondence_app
    {annotated : AnnotatedRelationTranslation.SyntaxRealizers}
    {univalent : DependentCalculus.UnivalentParametricitySequents.SyntaxRealizers}
    {context : UnderlyingDependentCalculus.Context n}
    {function function' argument argument' domain : UnderlyingDependentCalculus.Term n}
    {codomain : UnderlyingDependentCalculus.Term (n + 1)}
    {functionWitness argumentWitness :
      DependentCalculus.Term (DependentCalculus.RawParametricity.scopeSize n)}
    (functionCorrespondence :
      MaximalCorrespondence annotated univalent context function (.pi domain codomain)
        function' functionWitness)
    (argumentCorrespondence :
      MaximalCorrespondence annotated univalent context argument domain
        argument' argumentWitness) :
    MaximalCorrespondence annotated univalent context (.app function argument)
      (codomain.instantiate argument) (.app function' argument')
      (.app (.app (.app functionWitness
        (DependentCalculus.RawParametricity.original argument))
        (DependentCalculus.RawParametricity.primed argument')) argumentWitness) := by
  constructor
  · simpa only [DependentCalculus.RawParametricity.original,
      DependentCalculus.RawParametricity.primed, DependentCalculus.Term.rename] using
        DependentCalculus.UnivalentParametricitySequents.Sequent.app
          functionCorrespondence.univalent argumentCorrespondence.univalent
  · rw [Term.annotate_instantiate, Term.annotate_applyWitness]
    exact AnnotatedRelationTranslation.Judgment.app
      functionCorrespondence.annotated argumentCorrespondence.annotated

/-- Lambda abstraction preserves the canonical maximal correspondence. -/
theorem maximalCorrespondence_lam
    {annotated : AnnotatedRelationTranslation.SyntaxRealizers}
    {univalent : DependentCalculus.UnivalentParametricitySequents.SyntaxRealizers}
    {context : UnderlyingDependentCalculus.Context n}
    {domain domain' : UnderlyingDependentCalculus.Term n}
    {body codomain body' : UnderlyingDependentCalculus.Term (n + 1)}
    {level : Nat}
    {domainWitness :
      DependentCalculus.Term (DependentCalculus.RawParametricity.scopeSize n)}
    {bodyWitness :
      DependentCalculus.Term (DependentCalculus.RawParametricity.scopeSize n + 3)}
    (domainCorrespondence :
      MaximalCorrespondence annotated univalent context domain (.sort level)
        domain' domainWitness)
    (bodyCorrespondence :
      MaximalCorrespondence annotated univalent (.extend context domain) body codomain
        body' bodyWitness) :
    MaximalCorrespondence annotated univalent context (.lam domain body) (.pi domain codomain)
      (.lam domain' body')
      (DependentCalculus.ParametricitySequents.lambdaWitness
        (DependentCalculus.RawParametricity.original domain)
        (DependentCalculus.RawParametricity.primed domain')
        (DependentCalculus.ParametricitySequents.relatedDomain domainWitness)
        bodyWitness) := by
  constructor
  · have bodySequent :
        DependentCalculus.UnivalentParametricitySequents.Sequent univalent
          (AnnotatedParametricityErasure.eraseParametricityContext
            (Context.toTranslation context)).extend
          ((body.rename (DependentCalculus.Renaming.lift
            (DependentCalculus.RawParametricity.originalRenaming n))).rename
              DependentCalculus.ParametricitySequents.originalBinderRenaming)
          ((body'.rename (DependentCalculus.Renaming.lift
            (DependentCalculus.RawParametricity.primedRenaming n))).rename
              DependentCalculus.ParametricitySequents.primedBinderRenaming)
          bodyWitness := by
      simpa only [Context.toTranslation_extend,
        AnnotatedParametricityErasure.eraseParametricityContext_extend,
        DependentCalculus.RawParametricity.scopeSize,
        AnnotatedParametricityErasure.originalBody_underBinder,
        AnnotatedParametricityErasure.primedBody_underBinder] using
          bodyCorrespondence.univalent
    simpa only [DependentCalculus.RawParametricity.original,
      DependentCalculus.RawParametricity.primed, DependentCalculus.Term.rename] using
        DependentCalculus.UnivalentParametricitySequents.Sequent.lam
          domainCorrespondence.univalent bodySequent
  · rw [Term.annotate_lambdaWitness]
    exact AnnotatedRelationTranslation.Judgment.lam
      domainCorrespondence.annotated bodyCorrespondence.annotated

/-- Dependent products preserve the canonical maximal correspondence. -/
theorem maximalCorrespondence_pi
    {annotated : AnnotatedRelationTranslation.SyntaxRealizers}
    {univalent : DependentCalculus.UnivalentParametricitySequents.SyntaxRealizers}
    (agreement : RealizerAgreement annotated univalent)
    {context : UnderlyingDependentCalculus.Context n}
    {domain domain' : UnderlyingDependentCalculus.Term n}
    {codomain codomain' : UnderlyingDependentCalculus.Term (n + 1)}
    {level : Nat}
    {domainWitness :
      DependentCalculus.Term (DependentCalculus.RawParametricity.scopeSize n)}
    {codomainWitness :
      DependentCalculus.Term (DependentCalculus.RawParametricity.scopeSize n + 3)}
    (domainCorrespondence :
      MaximalCorrespondence annotated univalent context domain (.sort level)
        domain' domainWitness)
    (codomainCorrespondence :
      MaximalCorrespondence annotated univalent (.extend context domain) codomain
        (.sort level) codomain' codomainWitness) :
    MaximalCorrespondence annotated univalent context (.pi domain codomain) (.sort level)
      (.pi domain' codomain')
      (univalent.dependentProduct domainWitness codomainWitness) := by
  constructor
  · have codomainSequent :
        DependentCalculus.UnivalentParametricitySequents.Sequent univalent
          (AnnotatedParametricityErasure.eraseParametricityContext
            (Context.toTranslation context)).extend
          ((codomain.rename (DependentCalculus.Renaming.lift
            (DependentCalculus.RawParametricity.originalRenaming n))).rename
              DependentCalculus.ParametricitySequents.originalBinderRenaming)
          ((codomain'.rename (DependentCalculus.Renaming.lift
            (DependentCalculus.RawParametricity.primedRenaming n))).rename
              DependentCalculus.ParametricitySequents.primedBinderRenaming)
          codomainWitness := by
      simpa only [Context.toTranslation_extend,
        AnnotatedParametricityErasure.eraseParametricityContext_extend,
        DependentCalculus.RawParametricity.scopeSize,
        AnnotatedParametricityErasure.originalBody_underBinder,
        AnnotatedParametricityErasure.primedBody_underBinder] using
          codomainCorrespondence.univalent
    simpa only [DependentCalculus.RawParametricity.original,
      DependentCalculus.RawParametricity.primed, DependentCalculus.Term.rename] using
        DependentCalculus.UnivalentParametricitySequents.Sequent.pi
          domainCorrespondence.univalent codomainSequent
  · rw [← agreement.productRuleAgreement domain domain' codomain codomain'
      domainWitness codomainWitness]
    exact AnnotatedRelationTranslation.Judgment.pi rfl
      domainCorrespondence.annotated codomainCorrespondence.annotated

/-- Maximal subtyping conversion preserves the canonical correspondence and witness. -/
theorem maximalCorrespondence_conversion
    {annotated : AnnotatedRelationTranslation.SyntaxRealizers}
    {univalent : DependentCalculus.UnivalentParametricitySequents.SyntaxRealizers}
    (agreement : RealizerAgreement annotated univalent)
    {context : UnderlyingDependentCalculus.Context n}
    {term type type' term' : UnderlyingDependentCalculus.Term n}
    {witness : DependentCalculus.Term
      (DependentCalculus.RawParametricity.scopeSize n)}
    (correspondence :
      MaximalCorrespondence annotated univalent context term type term' witness)
    (subtype : UnderlyingDependentCalculus.Subtype context type type') :
    MaximalCorrespondence annotated univalent context term type' term' witness := by
  constructor
  · exact correspondence.univalent
  · rw [← agreement.weakeningAgreement subtype witness]
    exact AnnotatedRelationTranslation.Judgment.conversion
      correspondence.annotated (translatedSubtype subtype)

/-- A non-dependent arrow corresponds once its codomain translation is stable under weakening. -/
theorem maximalCorrespondence_arrow_of_liftedCodomain
    {annotated : AnnotatedRelationTranslation.SyntaxRealizers}
    {univalent : DependentCalculus.UnivalentParametricitySequents.SyntaxRealizers}
    (agreement : RealizerAgreement annotated univalent)
    {context : UnderlyingDependentCalculus.Context n}
    {domain domain' codomain codomain' : UnderlyingDependentCalculus.Term n}
    {level : Nat}
    {domainWitness :
      DependentCalculus.Term (DependentCalculus.RawParametricity.scopeSize n)}
    {liftedCodomainWitness :
      DependentCalculus.Term (DependentCalculus.RawParametricity.scopeSize n + 3)}
    (domainCorrespondence :
      MaximalCorrespondence annotated univalent context domain (.sort level)
        domain' domainWitness)
    (liftedCodomainCorrespondence :
      MaximalCorrespondence annotated univalent (.extend context domain)
        (codomain.rename DependentCalculus.Renaming.shift) (.sort level)
        (codomain'.rename DependentCalculus.Renaming.shift) liftedCodomainWitness) :
    MaximalCorrespondence annotated univalent context
      (UnderlyingDependentCalculus.Term.arrow domain codomain) (.sort level)
      (UnderlyingDependentCalculus.Term.arrow domain' codomain')
      (univalent.dependentProduct domainWitness liftedCodomainWitness) := by
  simpa only [UnderlyingDependentCalculus.Term.arrow] using
    maximalCorrespondence_pi agreement domainCorrespondence liftedCodomainCorrespondence

end ScopeBridge

end DeepWiki.Refine.MaximalAnnotation
