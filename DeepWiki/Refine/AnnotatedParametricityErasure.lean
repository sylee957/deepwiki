import DeepWiki.Refine.AnnotatedRelationTranslation
import DeepWiki.Refine.Parametricity.Sequents.Raw

/-! # Erasure of annotated translation to raw parametricity

Erasing an annotated translation context produces a raw parameter context. A relation-field
projection is propagated through applications and lambda bodies, yielding the raw witness carried
by the corresponding parametricity sequent. The erasure-only projection is a structural test model,
not a quotation of the primitive relation-record projection.
-/

namespace DeepWiki.Refine.AnnotatedParametricityErasure

open AnnotatedRelationTranslation
open DependentCalculus
open DependentCalculus.ParametricitySequents

/-- Object-language syntax for projecting the relation field of an annotated witness. -/
structure RelationFieldSyntax where
  /-- Project the relation field of one annotated witness term. -/
  relationField : {n : Nat} →
    AnnotatedDependentCalculus.Term n → DependentCalculus.Term n

/-- The erasure-only projection interprets every atomic annotated term by annotation erasure. -/
def RelationFieldSyntax.erasure : RelationFieldSyntax where
  relationField := AnnotatedDependentCalculus.Term.erase

/-- Recursively propagate relation-field projection through applications and lambda bodies. -/
def relationProjectionStar (projection : RelationFieldSyntax) :
    {n : Nat} → AnnotatedDependentCalculus.Term n → DependentCalculus.Term n
  | _, .app function argument =>
      .app (relationProjectionStar projection function)
        (relationProjectionStar projection argument)
  | _, .lam domain body =>
      .lam domain.erase (relationProjectionStar projection body)
  | _, term => projection.relationField term

/-- Projection-star distributes over application. -/
@[simp] theorem relationProjectionStar_app (projection : RelationFieldSyntax)
    (function argument : AnnotatedDependentCalculus.Term n) :
    relationProjectionStar projection (.app function argument) =
      .app (relationProjectionStar projection function)
        (relationProjectionStar projection argument) :=
  rfl

/-- Projection-star traverses a lambda body and erases its binder annotation. -/
@[simp] theorem relationProjectionStar_lam (projection : RelationFieldSyntax)
    (domain : AnnotatedDependentCalculus.Term n)
    (body : AnnotatedDependentCalculus.Term (n + 1)) :
    relationProjectionStar projection (.lam domain body) =
      .lam domain.erase (relationProjectionStar projection body) :=
  rfl

/-- The erasure-only projection agrees with ordinary annotation erasure on every term. -/
@[simp] theorem relationProjectionStar_erasure
    (term : AnnotatedDependentCalculus.Term n) :
    relationProjectionStar RelationFieldSyntax.erasure term = term.erase := by
  induction term with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [relationProjectionStar_app, AnnotatedDependentCalculus.Term.erase,
        functionInduction, argumentInduction]
  | lam domain body _ bodyInduction =>
      simp only [relationProjectionStar_lam, AnnotatedDependentCalculus.Term.erase,
        bodyInduction]
  | pi => rfl

/-- Erase an annotated translation context to its canonical raw variable triples. -/
def eraseParametricityContext : AnnotatedRelationTranslation.Context n →
    ParametricityContext (RawParametricity.scopeSize n)
  | .empty => []
  | .extend context _ => (eraseParametricityContext context).extend

/-- The raw variable triple corresponding to one source variable. -/
def rawTriple (index : Fin n) : VariableTriple (RawParametricity.scopeSize n) where
  original := RawParametricity.originalRenaming n index
  primed := RawParametricity.primedRenaming n index
  witness := RawParametricity.witnessRenaming n index

/-- Erasing a context extension extends its raw parameter context by one fresh triple. -/
@[simp] theorem eraseParametricityContext_extend
    (context : AnnotatedRelationTranslation.Context n)
    (type : AnnotatedDependentCalculus.Term n) :
    eraseParametricityContext (AnnotatedRelationTranslation.Context.extend context type) =
      (eraseParametricityContext context).extend :=
  rfl

/-- The erased parameter context is well formed. -/
theorem eraseParametricityContext_wellFormed
    (context : AnnotatedRelationTranslation.Context n) :
    (eraseParametricityContext context).WellFormed := by
  induction context with
  | empty => exact List.nodup_nil
  | extend context type inductionHypothesis => exact inductionHypothesis.extend

/-- Every source variable contributes its canonical raw triple to the erased context. -/
theorem rawTriple_mem (context : AnnotatedRelationTranslation.Context n)
    (index : Fin n) : rawTriple index ∈ eraseParametricityContext context := by
  induction context with
  | empty => exact Fin.elim0 index
  | @extend n context type inductionHypothesis =>
      refine Fin.cases ?_ (fun older => ?_) index
      · exact List.mem_cons_self
      · apply List.mem_cons_of_mem
        exact List.mem_map.mpr ⟨rawTriple older, inductionHypothesis older, rfl⟩

/-- Original-variable renaming beneath a source binder agrees with extending the raw context. -/
theorem originalRenaming_underBinder :
    DependentCalculus.Renaming.comp originalBinderRenaming
        (DependentCalculus.Renaming.lift (RawParametricity.originalRenaming n)) =
      RawParametricity.originalRenaming (n + 1) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

/-- Primed-variable renaming beneath a source binder agrees with extending the raw context. -/
theorem primedRenaming_underBinder :
    DependentCalculus.Renaming.comp primedBinderRenaming
        (DependentCalculus.Renaming.lift (RawParametricity.primedRenaming n)) =
      RawParametricity.primedRenaming (n + 1) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

/-- Renaming an original binder body into the extended raw scope gives its canonical copy. -/
theorem originalBody_underBinder (body : DependentCalculus.Term (n + 1)) :
    (body.rename (DependentCalculus.Renaming.lift
      (RawParametricity.originalRenaming n))).rename originalBinderRenaming =
        RawParametricity.original body := by
  rw [DependentCalculus.Term.rename_comp]
  exact DependentCalculus.Term.rename_congr originalRenaming_underBinder body

/-- Renaming a primed binder body into the extended raw scope gives its canonical copy. -/
theorem primedBody_underBinder (body : DependentCalculus.Term (n + 1)) :
    (body.rename (DependentCalculus.Renaming.lift
      (RawParametricity.primedRenaming n))).rename primedBinderRenaming =
        RawParametricity.primed body := by
  rw [DependentCalculus.Term.rename_comp]
  exact DependentCalculus.Term.rename_congr primedRenaming_underBinder body

/-- Laws connecting opaque annotated witness constructors to raw parametricity syntax. -/
structure ErasureLaws (realizers : SyntaxRealizers) (projection : RelationFieldSyntax) : Prop where
  /-- Projection-star leaves an embedded original source term unchanged after erasure. -/
  originalTerm : ∀ {n : Nat} (term : AnnotatedDependentCalculus.Term n),
    relationProjectionStar projection (AnnotatedRelationTranslation.Term.original term) =
      (AnnotatedRelationTranslation.Term.original term).erase
  /-- Projection-star leaves an embedded primed source term unchanged after erasure. -/
  primedTerm : ∀ {n : Nat} (term : AnnotatedDependentCalculus.Term n),
    relationProjectionStar projection (AnnotatedRelationTranslation.Term.primed term) =
      (AnnotatedRelationTranslation.Term.primed term).erase
  /-- Projecting a context relation variable yields the raw witness variable. -/
  relationVariable : ∀ {n : Nat} (index : Fin n),
    relationProjectionStar projection
        (.var (RawParametricity.witnessRenaming n index)) =
      .var (RawParametricity.witnessRenaming n index)
  /-- The projected annotated universe witness is the raw universe relation. -/
  universeWitness : ∀ {n : Nat} (source target : Annotation) (level : Nat),
    AdmissibleUniverseTranslation source target →
    relationProjectionStar projection
        (realizers.universeRule (n := n) source target level) =
      RawParametricity.sortRelation level (RawParametricity.scopeSize n)
  /-- Projecting an opaque arrow realizer preserves raw arrow translation. -/
  arrowWitness : ∀ {n : Nat} (context : AnnotatedRelationTranslation.Context n)
      (output : Annotation)
      (domain domain' codomain codomain' : AnnotatedDependentCalculus.Term n)
      (domainWitness codomainWitness : AnnotatedDependentCalculus.Term
        (RawParametricity.scopeSize n)),
    RawSequent (eraseParametricityContext context)
      (AnnotatedRelationTranslation.Term.original domain).erase
      (AnnotatedRelationTranslation.Term.primed domain').erase
      (relationProjectionStar projection domainWitness) →
    RawSequent (eraseParametricityContext context)
      (AnnotatedRelationTranslation.Term.original codomain).erase
      (AnnotatedRelationTranslation.Term.primed codomain').erase
      (relationProjectionStar projection codomainWitness) →
    RawSequent (eraseParametricityContext context)
      (AnnotatedRelationTranslation.Term.original
        (AnnotatedRelationTranslation.Term.arrow domain codomain)).erase
      (AnnotatedRelationTranslation.Term.primed
        (AnnotatedRelationTranslation.Term.arrow domain' codomain')).erase
      (relationProjectionStar projection
        (realizers.arrow output domain domain' codomain codomain'
          domainWitness codomainWitness))
  /-- Projecting an opaque dependent-product realizer preserves raw product translation. -/
  piWitness : ∀ {n : Nat} (context : AnnotatedRelationTranslation.Context n)
      (output : Annotation)
      (domain domain' : AnnotatedDependentCalculus.Term n)
      (codomain codomain' : AnnotatedDependentCalculus.Term (n + 1))
      (domainWitness : AnnotatedDependentCalculus.Term (RawParametricity.scopeSize n))
      (codomainWitness : AnnotatedDependentCalculus.Term
        (RawParametricity.scopeSize n + 3)),
    RawSequent (eraseParametricityContext context)
      (AnnotatedRelationTranslation.Term.original domain).erase
      (AnnotatedRelationTranslation.Term.primed domain').erase
      (relationProjectionStar projection domainWitness) →
    RawSequent (eraseParametricityContext (.extend context domain))
      (AnnotatedRelationTranslation.Term.original codomain).erase
      (AnnotatedRelationTranslation.Term.primed codomain').erase
      (relationProjectionStar projection codomainWitness) →
    RawSequent (eraseParametricityContext context)
      (AnnotatedRelationTranslation.Term.original
        (AnnotatedDependentCalculus.Term.pi domain codomain)).erase
      (AnnotatedRelationTranslation.Term.primed
        (AnnotatedDependentCalculus.Term.pi domain' codomain')).erase
      (relationProjectionStar projection
        (realizers.pi output domain domain' codomain codomain'
          domainWitness codomainWitness))
  /-- Projecting witness weakening forgets the annotation change. -/
  weakeningWitness : ∀ {n : Nat} (context : AnnotatedRelationTranslation.Context n)
      {source target : AnnotatedDependentCalculus.Term n}
      (subtype : AnnotatedDependentCalculus.Subtype context.gamma source target)
      (witness : AnnotatedDependentCalculus.Term (RawParametricity.scopeSize n)),
    relationProjectionStar projection (realizers.weakening context subtype witness) =
      relationProjectionStar projection witness

/-- A universe-witness quote collides when it is syntactically an embedded ordinary term. -/
theorem noErasureLaws_of_universeWitness_collision
    {realizers : SyntaxRealizers} {projection : RelationFieldSyntax}
    {source target : Annotation} {level n : Nat}
    (admissible : AdmissibleUniverseTranslation source target)
    (term : AnnotatedDependentCalculus.Term n)
    (collision : realizers.universeRule source target level =
      AnnotatedRelationTranslation.Term.original term)
    (different : (AnnotatedRelationTranslation.Term.original term).erase ≠
      RawParametricity.sortRelation level (RawParametricity.scopeSize n)) :
    ¬ ErasureLaws realizers projection := by
  intro laws
  apply different
  rw [← laws.universeWitness source target level admissible, collision]
  exact (laws.originalTerm term).symm

example (term : AnnotatedDependentCalculus.Term n) :
    relationProjectionStar RelationFieldSyntax.erasure term = term.erase :=
  relationProjectionStar_erasure term

example {realizers : SyntaxRealizers} {projection : RelationFieldSyntax}
    {source target : Annotation} {level n : Nat}
    (admissible : AdmissibleUniverseTranslation source target)
    (term : AnnotatedDependentCalculus.Term n)
    (collision : realizers.universeRule source target level =
      AnnotatedRelationTranslation.Term.original term)
    (different : (AnnotatedRelationTranslation.Term.original term).erase ≠
      RawParametricity.sortRelation level (RawParametricity.scopeSize n)) :
    ¬ ErasureLaws realizers projection :=
  noErasureLaws_of_universeWitness_collision admissible term collision different

/-- Erasing an annotated translation derivation yields its raw parametricity sequent. -/
theorem Judgment.eraseToRaw {realizers : SyntaxRealizers} {projection : RelationFieldSyntax}
    (laws : ErasureLaws realizers projection)
    {context : AnnotatedRelationTranslation.Context n}
    {term type term' : AnnotatedDependentCalculus.Term n}
    {witness : AnnotatedDependentCalculus.Term (RawParametricity.scopeSize n)}
    (translation : Judgment realizers context term type term' witness) :
    RawSequent (eraseParametricityContext context)
      (AnnotatedRelationTranslation.Term.original term).erase
      (AnnotatedRelationTranslation.Term.primed term').erase
      (relationProjectionStar projection witness) := by
  induction translation with
  | sort admissible level =>
      rw [laws.universeWitness _ _ _ admissible]
      exact .paramSort _ level
  | @var _ context entry member contextWellFormed =>
      have entryIndex : ∃ index, context.entryAt index = entry := by
        simpa only [AnnotatedRelationTranslation.Context.Contains,
          AnnotatedRelationTranslation.Context.entries, List.mem_ofFn] using member
      obtain ⟨index, rfl⟩ := entryIndex
      simp only [AnnotatedRelationTranslation.Context.entryAt]
      rw [laws.relationVariable index]
      simpa only [AnnotatedRelationTranslation.Term.original,
        AnnotatedRelationTranslation.Term.primed,
        rawTriple,
        AnnotatedDependentCalculus.Term.rename,
        AnnotatedDependentCalculus.Term.erase] using
          RawSequent.paramVar (eraseParametricityContext_wellFormed context)
            (rawTriple_mem context index)
  | app functionTranslation argumentTranslation functionInduction argumentInduction =>
      rw [Term.applyWitness, relationProjectionStar_app,
        relationProjectionStar_app, relationProjectionStar_app,
        laws.originalTerm, laws.primedTerm]
      simpa only [
        AnnotatedRelationTranslation.Term.original,
        AnnotatedRelationTranslation.Term.primed,
        AnnotatedDependentCalculus.Term.rename,
        AnnotatedDependentCalculus.Term.erase] using
          RawSequent.paramApp functionInduction argumentInduction
  | @lam n context domain domain' body codomain body' level annotation
      domainWitness bodyWitness domainTranslation bodyTranslation
      domainInduction bodyInduction =>
      have bodySequent :
          RawSequent (eraseParametricityContext context).extend
            ((body.erase.rename (DependentCalculus.Renaming.lift
              (RawParametricity.originalRenaming n))).rename originalBinderRenaming)
            ((body'.erase.rename (DependentCalculus.Renaming.lift
              (RawParametricity.primedRenaming n))).rename primedBinderRenaming)
            (relationProjectionStar projection bodyWitness) := by
        simpa only [eraseParametricityContext_extend,
          RawParametricity.scopeSize,
          AnnotatedRelationTranslation.Term.erase_original,
          AnnotatedRelationTranslation.Term.erase_primed,
          RawParametricity.original, RawParametricity.primed,
          originalBody_underBinder, primedBody_underBinder] using bodyInduction
      have lambdaSequent := RawSequent.paramLam
        (domain := (AnnotatedRelationTranslation.Term.original domain).erase)
        (primedDomain := (AnnotatedRelationTranslation.Term.primed domain').erase)
        (witnessDomain := (domainWitness.relatedDomain).erase) bodySequent
      simpa only [AnnotatedRelationTranslation.Term.lambdaWitness,
        relationProjectionStar_lam, AnnotatedDependentCalculus.Term.erase,
        DependentCalculus.Term.rename,
        AnnotatedRelationTranslation.Term.erase_original,
        AnnotatedRelationTranslation.Term.erase_primed,
        AnnotatedRelationTranslation.Term.erase_weakenBy,
        AnnotatedRelationTranslation.Term.erase_relatedDomain,
        RawParametricity.original, RawParametricity.primed,
        originalBody_underBinder, primedBody_underBinder,
        ParametricitySequents.lambdaWitness] using lambdaSequent
  | arrow requirements domainTranslation codomainTranslation
      domainInduction codomainInduction =>
      exact laws.arrowWitness _ _ _ _ _ _ _ _ domainInduction codomainInduction
  | pi requirements domainTranslation codomainTranslation
      domainInduction codomainInduction =>
      exact laws.piWitness _ _ _ _ _ _ _ _ domainInduction codomainInduction
  | conversion translation subtype inductionHypothesis =>
      rw [laws.weakeningWitness]
      exact inductionHypothesis

end DeepWiki.Refine.AnnotatedParametricityErasure
