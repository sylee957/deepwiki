import DeepWiki.Refine.Parametricity.Raw.RelationTypes

/-! # Typing the raw parametricity translation

Translated contexts and original, primed, and witness terms support constructor-by-constructor typing.
-/

namespace DeepWiki.Refine.DependentCalculus.RawParametricity

open DeepWiki.Refine.CCOmega.SurfaceSyntax

/-- Translation preserves well-formedness of the empty context. -/
theorem context_empty_wellFormed : WellFormed (context (ccωctx!{ ⟨⟩ })) :=
  WellFormed.empty

/-- Original-variable lookup in a translated context equals renaming the source lookup. -/
theorem context_lookup_original (source : Context n) (index : Fin n) :
    (context source).lookup (originalRenaming n index) =
      (source.lookup index).rename (originalRenaming n) := by
  induction source with
  | empty => exact Fin.elim0 index
  | @extend n source type inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · change
          (((type.rename (originalRenaming n)).rename Renaming.shift).rename
              Renaming.shift).rename Renaming.shift =
            (type.rename Renaming.shift).rename (originalRenaming (n + 1))
        simp only [Term.rename_comp]
        apply Term.rename_congr
        funext older
        rfl
      · intro older
        change
          ((((context source).lookup (originalRenaming n older)).rename
              Renaming.shift).rename Renaming.shift).rename Renaming.shift =
            ((source.lookup older).rename Renaming.shift).rename
              (originalRenaming (n + 1))
        rw [inductionHypothesis older]
        simp only [Term.rename_comp]
        apply Term.rename_congr
        funext element
        rfl

/-- Primed-variable lookup in a translated context equals renaming the source lookup. -/
theorem context_lookup_primed (source : Context n) (index : Fin n) :
    (context source).lookup (primedRenaming n index) =
      (source.lookup index).rename (primedRenaming n) := by
  induction source with
  | empty => exact Fin.elim0 index
  | @extend n source type inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · change
          (((type.rename (primedRenaming n)).rename Renaming.shift).rename
              Renaming.shift).rename Renaming.shift =
            (type.rename Renaming.shift).rename (primedRenaming (n + 1))
        simp only [Term.rename_comp]
        apply Term.rename_congr
        funext older
        rfl
      · intro older
        change
          ((((context source).lookup (primedRenaming n older)).rename
              Renaming.shift).rename Renaming.shift).rename Renaming.shift =
            ((source.lookup older).rename Renaming.shift).rename
              (primedRenaming (n + 1))
        rw [inductionHypothesis older]
        simp only [Term.rename_comp]
        apply Term.rename_congr
        funext element
        rfl

/-- Original-variable embedding is typed whenever the translated target context is well formed. -/
theorem originalTypedRenaming (source : Context n)
    (translatedWellFormed : WellFormed (context source)) :
    TypedRenaming source (context source) (originalRenaming n) where
  targetWellFormed := translatedWellFormed
  lookup_eq := context_lookup_original source

/-- Primed-variable embedding is typed whenever the translated target context is well formed. -/
theorem primedTypedRenaming (source : Context n)
    (translatedWellFormed : WellFormed (context source)) :
    TypedRenaming source (context source) (primedRenaming n) where
  targetWellFormed := translatedWellFormed
  lookup_eq := context_lookup_primed source

/-- Original-copy renaming preserves a typing derivation into a well-formed translated context. -/
theorem HasType.original {source : Context n} {term type : Term n}
    (termWellTyped : HasType source term type)
    (translatedWellFormed : WellFormed (context source)) :
    HasType (context source) (original term) (original type) :=
  termWellTyped.rename (originalTypedRenaming source translatedWellFormed)

/-- Primed-copy renaming preserves a typing derivation into a well-formed translated context. -/
theorem HasType.primed {source : Context n} {term type : Term n}
    (termWellTyped : HasType source term type)
    (translatedWellFormed : WellFormed (context source)) :
    HasType (context source) (primed term) (primed type) :=
  termWellTyped.rename (primedTypedRenaming source translatedWellFormed)

/-- A typed product translation makes its beta-normal relation fiber universe-typed. -/
theorem piRelationFiber_hasType_of_productTranslation {source : Context n}
    {function domain : Term n} {codomain : Term (n + 1)} {translationType : Term (scopeSize n)}
    (translatedWellFormed : WellFormed (context source))
    (functionWellTyped :
      HasType source function (ccω!{ Π x : %{domain}, %{codomain} }))
    (translatedProductWellTyped :
      HasType (context source)
        (translate (ccω!{ Π x : %{domain}, %{codomain} })) translationType) :
    ∃ level,
      HasType (context source) (piRelationFiber domain codomain function)
        (.sort level) := by
  rw [translate_pi_body] at translatedProductWellTyped
  obtain ⟨_, _, _, secondLambdaWellTyped⟩ :=
    translatedProductWellTyped.lamComponents
  have secondLambdaInstantiated := secondLambdaWellTyped.instantiate
    translatedWellFormed (HasType.original functionWellTyped translatedWellFormed)
  rw [instantiate_piRelation_secondLambda] at secondLambdaInstantiated
  obtain ⟨_, _, _, relationBodyWellTyped⟩ :=
    secondLambdaInstantiated.lamComponents
  have relationFiberWellTyped := relationBodyWellTyped.instantiate
    translatedWellFormed (HasType.primed functionWellTyped translatedWellFormed)
  change HasType (context source) (piRelationFiber domain codomain function) _ at relationFiberWellTyped
  obtain ⟨domainLevel, codomainLevel, domainWellTyped, codomainWellTyped⟩ :=
    relationFiberWellTyped.piComponents
  exact ⟨max domainLevel codomainLevel,
    HasType.pi domainWellTyped codomainWellTyped⟩

/-- The beta-normal relation fiber of a translated dependent function is universe-typed. -/
theorem piRelationFiber_hasType {source : Context n} {function domain : Term n}
    {codomain : Term (n + 1)}
    (translatedWellFormed : WellFormed (context source))
    (functionWellTyped :
      HasType source function (ccω!{ Π x : %{domain}, %{codomain} }))
    (functionWitness :
      HasType (context source) (translate function)
        (relatedTermType function (ccω!{ Π x : %{domain}, %{codomain} }))) :
    ∃ level,
      HasType (context source) (piRelationFiber domain codomain function)
        (.sort level) := by
  obtain ⟨_, relationTypeWellTyped⟩ := functionWitness.typeWellTyped
  change HasType (context source)
    (ccω!{
      %{translate (.pi domain codomain)}
      %{original function}
      %{primed function} }) _ at relationTypeWellTyped
  obtain ⟨_, _, firstApplicationWellTyped, _⟩ :=
    relationTypeWellTyped.appComponents
  obtain ⟨_, _, translatedProductWellTyped, _⟩ :=
    firstApplicationWellTyped.appComponents
  exact piRelationFiber_hasType_of_productTranslation translatedWellFormed
    functionWellTyped translatedProductWellTyped

/-- Application preserves the witness-typing conclusion of raw abstraction. -/
theorem translate_app_witness_hasType {source : Context n}
    {function argument domain : Term n} {codomain : Term (n + 1)}
    (translatedWellFormed : WellFormed (context source))
    (functionWellTyped :
      HasType source function (ccω!{ Π x : %{domain}, %{codomain} }))
    (argumentWellTyped : HasType source argument domain)
    (functionWitness :
      HasType (context source) (translate function)
        (relatedTermType function (ccω!{ Π x : %{domain}, %{codomain} })))
    (argumentWitness :
      HasType (context source) (translate argument)
        (relatedTermType argument domain)) :
    HasType (context source) (translate (ccω!{ %{function} %{argument} }))
      (relatedTermType (ccω!{ %{function} %{argument} })
        (codomain.instantiate argument)) := by
  obtain ⟨_, relationFiberWellTyped⟩ :=
    piRelationFiber_hasType translatedWellFormed functionWellTyped functionWitness
  have functionWitnessNormal :
      HasType (context source) (translate function)
        (piRelationFiber domain codomain function) :=
    .conversion functionWitness relationFiberWellTyped
      (relatedTermType_pi_beta function domain codomain)
  rw [piRelationFiber_eq_normal] at functionWitnessNormal
  have appliedOriginal := HasType.app functionWitnessNormal
    (HasType.original argumentWellTyped translatedWellFormed)
  have primedDomainInstantiated :
      (weakenBy (primed domain) 1).substitute
          (Substitution.single (original argument)) =
        primed domain := by
    simpa only [weakenBy] using
      substitute_single_rename_shift (primed domain) (original argument)
  simp only [Term.instantiate, Term.substitute] at appliedOriginal
  rw [primedDomainInstantiated] at appliedOriginal
  have appliedPrimed := HasType.app appliedOriginal
    (HasType.primed argumentWellTyped translatedWellFormed)
  have relatedDomainInstantiated :=
    substitute_binaryRelation_functionCopies (translate domain) argument
  simp only [Term.substitute] at relatedDomainInstantiated
  simp only [Term.instantiate, Term.substitute] at appliedPrimed
  rw [relatedDomainInstantiated] at appliedPrimed
  have appliedWitness := HasType.app appliedPrimed argumentWitness
  have appliedWitnessBody :
      HasType (context source) (translate (ccω!{ %{function} %{argument} }))
        ((((applicationRelationBody function codomain).substitute
            (Substitution.lift
              (Substitution.lift (Substitution.single (original argument))))).substitute
          (Substitution.lift (Substitution.single (primed argument)))).instantiate
            (translate argument)) := by
    simpa only [applicationRelationBody, translate_app, Term.substitute] using appliedWitness
  change HasType (context source) (translate (ccω!{ %{function} %{argument} }))
    ((((applicationRelationBody function codomain).substitute
          (Substitution.lift
            (Substitution.lift (Substitution.single (original argument))))).substitute
        (Substitution.lift (Substitution.single (primed argument)))).substitute
      (Substitution.single (translate argument))) at appliedWitnessBody
  rw [substitute_relationalSingle, applicationRelationBody_substitute] at appliedWitnessBody
  exact appliedWitnessBody

/-- A translated context assigns every witness variable its related-term type. -/
theorem context_lookup_witness (source : Context n) (index : Fin n) :
    (context source).lookup (witnessRenaming n index) =
      relatedTermType (.var index) (source.lookup index) := by
  induction source with
  | empty => exact Fin.elim0 index
  | @extend n source type inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · rw [show
          (context (.extend source type)).lookup (witnessRenaming (n + 1) 0) =
            .app (.app (weakenBy (translate type) 3)
              (.var (originalRenaming (n + 1) 0)))
              (.var (primedRenaming (n + 1) 0)) by
              rfl]
        rw [weakenBy_three_eq_rename_translatedShift]
        have translatedTypeNatural :
            (translate type).rename (translatedShift n) =
              translate (type.rename Renaming.shift) := by
          simpa only [relationalShift] using
            (translate_rename (relationalShift n) type).symm
        simpa only [relatedTermType, Context.lookup, original_var, primed_var,
          finCases_zero] using congrArg
            (fun relation =>
              Term.app (Term.app relation (.var (originalRenaming (n + 1) 0)))
                (.var (primedRenaming (n + 1) 0)))
            translatedTypeNatural
      · intro older
        rw [show
          (context (.extend source type)).lookup (witnessRenaming (n + 1) older.succ) =
            weakenBy ((context source).lookup (witnessRenaming n older)) 3 by
              rfl]
        rw [inductionHypothesis older, weakenBy_three_eq_rename_translatedShift]
        simpa only [relationalShift, Context.lookup, Term.rename,
          Renaming.shift, finCases_succ] using
          (relatedTermType_rename (relationalShift n) (.var older)
            (source.lookup older)).symm

/-- A translated universe relation applied to two translated types is itself universe-typed. -/
theorem relatedType_hasType {source : Context n} {type : Term n} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (typeWellTyped : HasType source type (.sort level)) :
    HasType (context source) (relatedTermType type (.sort level))
      (.sort (level + 1)) := by
  have relationConstructor :
      HasType (context source) (translate (.sort level : Term n))
        (sortRelationType level (scopeSize n)) := by
    exact .conversion (translate_sort_hasType translatedWellFormed level)
      (sortRelationType_hasType translatedWellFormed level)
      (translatedSortType_beta level n)
  have originalType := HasType.original typeWellTyped translatedWellFormed
  have primedType := HasType.primed typeWellTyped translatedWellFormed
  have firstApplication := HasType.app relationConstructor originalType
  have secondApplication := HasType.app firstApplication primedType
  simpa only [relatedTermType, sortRelationType, Term.instantiate, Term.substitute,
    Substitution.single, Term.rename] using secondApplication

/-- The element-relation type is well typed whenever its source type is. -/
theorem elementRelationType_hasType {source : Context n} {type : Term n} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (typeWellTyped : HasType source type (.sort level)) :
    HasType (context source) (elementRelationType type level)
      (.sort (level + 1)) := by
  have originalType := HasType.original typeWellTyped translatedWellFormed
  have firstWellFormed : WellFormed (.extend (context source) (original type)) :=
    .extend translatedWellFormed originalType
  have primedType := HasType.primed typeWellTyped translatedWellFormed
  have weakenedPrimedType := primedType.weaken firstWellFormed
  have secondWellFormed :
      WellFormed
        (.extend (.extend (context source) (original type))
          (weakenBy (primed type) 1)) := by
    simpa only [weakenBy, primed, Term.rename] using
      WellFormed.extend firstWellFormed weakenedPrimedType
  have resultSort :
      HasType
        (.extend (.extend (context source) (original type))
          (weakenBy (primed type) 1))
        (.sort level) (.sort (level + 1)) :=
    .sort secondWellFormed level
  have innerProduct := HasType.pi
    (by simpa only [weakenBy, primed, Term.rename] using weakenedPrimedType)
    resultSort
  have outerProduct := HasType.pi originalType innerProduct
  simpa only [elementRelationType, Nat.max_eq_right (Nat.le_succ level)] using outerProduct

/-- A translated source type has its beta-normal binary element-relation type. -/
theorem translate_type_hasType_normal {source : Context n} {type : Term n} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (typeWellTyped : HasType source type (.sort level))
    (witnessWellTyped :
      HasType (context source) (translate type) (relatedTermType type (.sort level))) :
    HasType (context source) (translate type) (elementRelationType type level) :=
  .conversion witnessWellTyped
    (elementRelationType_hasType translatedWellFormed typeWellTyped)
    (relatedTermType_sort_beta type level)

/-- A translated type witness makes the corresponding related-term type universe-typed. -/
theorem relatedTermType_hasType_of_typeWitness {source : Context n}
    {term type : Term n} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (termWellTyped : HasType source term type)
    (typeWellTyped : HasType source type (.sort level))
    (typeWitness : HasType (context source) (translate type)
      (relatedTermType type (.sort level))) :
    HasType (context source) (relatedTermType term type) (.sort level) := by
  have relationNormal := translate_type_hasType_normal translatedWellFormed
    typeWellTyped typeWitness
  have appliedOriginal := HasType.app relationNormal
    (HasType.original termWellTyped translatedWellFormed)
  have primedTypeInstantiated :
      (weakenBy (primed type) 1).substitute
          (Substitution.single (original term)) = primed type := by
    simpa only [weakenBy] using
      substitute_single_rename_shift (primed type) (original term)
  simp only [Term.instantiate, Term.substitute] at appliedOriginal
  rw [primedTypeInstantiated] at appliedOriginal
  have appliedBoth := HasType.app appliedOriginal
    (HasType.primed termWellTyped translatedWellFormed)
  simpa only [relatedTermType, elementRelationType, Term.instantiate,
    Term.substitute, Substitution.single, weakenBy,
    substitute_single_rename_shift] using appliedBoth

/-- A translated context extension is well formed once the source type witness is typed. -/
theorem context_extend_wellFormed {source : Context n} {type : Term n} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (typeWellTyped : HasType source type (.sort level))
    (witnessWellTyped :
      HasType (context source) (translate type) (relatedTermType type (.sort level))) :
    WellFormed (context (ccωctx!{ %{source}, x : %{type} })) := by
  have originalType := HasType.original typeWellTyped translatedWellFormed
  have firstWellFormed : WellFormed (.extend (context source) (original type)) :=
    .extend translatedWellFormed originalType
  have primedType := HasType.primed typeWellTyped translatedWellFormed
  have weakenedPrimedType := primedType.weaken firstWellFormed
  have secondWellFormed :
      WellFormed
        (.extend (.extend (context source) (original type))
          (weakenBy (primed type) 1)) := by
    simpa only [weakenBy, primed, Term.rename] using
      WellFormed.extend firstWellFormed weakenedPrimedType
  have relationWellTyped :=
    translate_type_hasType_normal translatedWellFormed typeWellTyped witnessWellTyped
  have relationWeakenedOnce := relationWellTyped.weaken firstWellFormed
  have relationWeakenedTwice := relationWeakenedOnce.weaken secondWellFormed
  have originalVariable := HasType.var secondWellFormed (1 : Fin (scopeSize n + 2))
  have firstApplicationRaw := HasType.app relationWeakenedTwice originalVariable
  have firstApplication :
      HasType
        (.extend (.extend (context source) (original type))
          (weakenBy (primed type) 1))
        (.app (weakenBy (translate type) 2) (.var 1))
        (.pi (weakenBy (primed type) 2) (.sort level)) := by
    simpa only [elementRelationType, weakenBy, Term.rename, Context.lookup,
      instantiate_pi_double_lift_shift] using
        firstApplicationRaw
  have primedVariable := HasType.var secondWellFormed (0 : Fin (scopeSize n + 2))
  have witnessTypeWellTyped := HasType.app firstApplication primedVariable
  simpa only [context_extend, scopeSize, elementRelationType, weakenBy, Term.rename,
    Context.lookup, Term.instantiate, Term.substitute, Substitution.single,
    Substitution.lift, finCases_zero, finCases_one,
    substitute_single_rename_shift] using
      WellFormed.extend secondWellFormed witnessTypeWellTyped

/-- The body of a translated dependent-product relation has the source product's universe level. -/
theorem piRelationBody_hasType {source : Context n}
    {domain : Term n} {codomain : Term (n + 1)}
    {domainLevel codomainLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped : HasType source domain (.sort domainLevel))
    (codomainWellTyped :
      HasType (ccωctx!{ %{source}, x : %{domain} }) codomain (.sort codomainLevel))
    (domainWitness :
      HasType (context source) (translate domain)
        (relatedTermType domain (.sort domainLevel)))
    (codomainWitness :
      HasType (context (ccωctx!{ %{source}, x : %{domain} })) (translate codomain)
        (relatedTermType codomain (.sort codomainLevel))) :
    HasType
      (ccωctx!{
        %{context source},
        f0 : %{original (.pi domain codomain)},
        f1 : %{weakenBy (primed (.pi domain codomain)) 1} })
      (piRelationBody domain codomain)
      (.sort (max domainLevel codomainLevel)) := by
  have productWellTyped := HasType.pi domainWellTyped codomainWellTyped
  have originalProduct := HasType.original productWellTyped translatedWellFormed
  have firstWellFormed := WellFormed.extend translatedWellFormed originalProduct
  have primedProduct := HasType.primed productWellTyped translatedWellFormed
  have primedProductWeakened := primedProduct.weaken firstWellFormed
  have secondWellFormed :
      WellFormed
        (.extend
          (.extend (context source) (original (.pi domain codomain)))
          (weakenBy (primed (.pi domain codomain)) 1)) := by
    simpa only [weakenBy, primed, Term.rename] using
      WellFormed.extend firstWellFormed primedProductWeakened
  have baseInsertion :
      TypedRenaming (context source)
        (.extend
          (.extend (context source) (original (.pi domain codomain)))
          (weakenBy (primed (.pi domain codomain)) 1))
        (Renaming.comp Renaming.shift Renaming.shift) := by
    exact TypedRenaming.comp (TypedRenaming.shift secondWellFormed)
      (TypedRenaming.shift firstWellFormed)
  have originalDomain := HasType.original domainWellTyped translatedWellFormed
  have originalDomainInserted :
      HasType
        (.extend
          (.extend (context source) (original (.pi domain codomain)))
          (weakenBy (primed (.pi domain codomain)) 1))
        ((original domain).rename (Renaming.comp Renaming.shift Renaming.shift))
        (.sort domainLevel) := by
    simpa only [original, Term.rename] using originalDomain.rename baseInsertion
  let insertionOne := baseInsertion.lift originalDomainInserted
  have sourceFirstWellFormed := WellFormed.extend translatedWellFormed originalDomain
  have primedDomain := HasType.primed domainWellTyped translatedWellFormed
  have primedDomainSource :
      HasType (.extend (context source) (original domain))
        (weakenBy (primed domain) 1) (.sort domainLevel) := by
    simpa only [weakenBy, primed, Term.rename] using
      primedDomain.weaken sourceFirstWellFormed
  have sourceSecondWellFormed :=
    WellFormed.extend sourceFirstWellFormed primedDomainSource
  have primedDomainInserted := primedDomainSource.rename insertionOne
  let insertionTwo := insertionOne.lift primedDomainInserted
  have relationDomainSource :
      HasType
        (.extend (.extend (context source) (original domain))
          (weakenBy (primed domain) 1))
        (.app (.app (weakenBy (translate domain) 2) (.var 1)) (.var 0))
        (.sort domainLevel) := by
    have relationWellTyped := translate_type_hasType_normal
      translatedWellFormed domainWellTyped domainWitness
    have relationWeakenedOnce := relationWellTyped.weaken sourceFirstWellFormed
    have relationWeakenedTwice := relationWeakenedOnce.weaken sourceSecondWellFormed
    have originalVariable := HasType.var sourceSecondWellFormed
      (1 : Fin (scopeSize n + 2))
    have firstApplicationRaw := HasType.app relationWeakenedTwice originalVariable
    have firstApplication :
        HasType
          (.extend (.extend (context source) (original domain))
            (weakenBy (primed domain) 1))
          (.app (weakenBy (translate domain) 2) (.var 1))
          (.pi (weakenBy (primed domain) 2) (.sort domainLevel)) := by
      simpa only [elementRelationType, weakenBy, Term.rename, Context.lookup,
        instantiate_pi_double_lift_shift] using firstApplicationRaw
    have primedVariable := HasType.var sourceSecondWellFormed
      (0 : Fin (scopeSize n + 2))
    have relationApplication := HasType.app firstApplication primedVariable
    simpa only [Term.instantiate, Term.substitute, Substitution.single,
      Substitution.lift, finCases_zero, finCases_one,
      substitute_single_rename_shift, weakenBy] using relationApplication
  have relationDomainInserted := relationDomainSource.rename insertionTwo
  let insertionThree := insertionTwo.lift relationDomainInserted
  have sourceTripleWellFormed := context_extend_wellFormed
    translatedWellFormed domainWellTyped domainWitness
  have codomainRelationNormal := translate_type_hasType_normal
    sourceTripleWellFormed codomainWellTyped codomainWitness
  have codomainRelationInserted := codomainRelationNormal.rename insertionThree
  change HasType _
    ((translate codomain).rename
      (Renaming.lift (Renaming.lift (Renaming.lift
        (Renaming.comp Renaming.shift Renaming.shift)))))
    (.pi
      ((original codomain).rename
        (Renaming.lift (Renaming.lift (Renaming.lift
          (Renaming.comp Renaming.shift Renaming.shift)))))
      (.pi
        ((weakenBy (primed codomain) 1).rename
          (Renaming.lift (Renaming.lift (Renaming.lift (Renaming.lift
            (Renaming.comp Renaming.shift Renaming.shift))))))
        (.sort codomainLevel))) at codomainRelationInserted
  have targetWellFormed := insertionThree.targetWellFormed
  have originalFunction := HasType.var targetWellFormed
    (4 : Fin (scopeSize n + 5))
  have originalArgument := HasType.var targetWellFormed
    (2 : Fin (scopeSize n + 5))
  change HasType _ (.var 2)
    (((((original domain).rename (Renaming.comp Renaming.shift Renaming.shift)).rename
      Renaming.shift).rename Renaming.shift).rename Renaming.shift) at originalArgument
  have originalArgumentType :
      (((((original domain).rename (Renaming.comp Renaming.shift Renaming.shift)).rename
        Renaming.shift).rename Renaming.shift).rename Renaming.shift) =
        weakenBy (original domain) 5 := by
    simp only [weakenBy, Term.rename_comp]
  rw [originalArgumentType] at originalArgument
  have originalApplication := HasType.app originalFunction originalArgument
  rw [original_codomain_insert_target] at originalApplication
  have primedFunction := HasType.var targetWellFormed
    (3 : Fin (scopeSize n + 5))
  have primedArgument := HasType.var targetWellFormed
    (1 : Fin (scopeSize n + 5))
  change HasType _ (.var 1)
    ((((weakenBy (primed domain) 1).rename
      (Renaming.lift (Renaming.comp Renaming.shift Renaming.shift))).rename
      Renaming.shift).rename Renaming.shift) at primedArgument
  have primedArgumentType :
      ((((weakenBy (primed domain) 1).rename
        (Renaming.lift (Renaming.comp Renaming.shift Renaming.shift))).rename
        Renaming.shift).rename Renaming.shift) =
        weakenBy (primed domain) 5 := by
    simp only [weakenBy, Term.rename_comp]
    apply Term.rename_congr
    funext index
    rfl
  rw [primedArgumentType] at primedArgument
  have primedApplication := HasType.app primedFunction primedArgument
  rw [primed_codomain_insert_target] at primedApplication
  have codomainAppliedOriginal := HasType.app codomainRelationInserted originalApplication
  simp only [Term.instantiate, Term.substitute] at codomainAppliedOriginal
  rw [substitute_inserted_primed_codomain] at codomainAppliedOriginal
  have codomainAppliedBoth := HasType.app codomainAppliedOriginal primedApplication
  have relationProduct := HasType.pi relationDomainInserted codomainAppliedBoth
  have primedProductBody := HasType.pi primedDomainInserted relationProduct
  have originalProductBody := HasType.pi originalDomainInserted primedProductBody
  have originalDomainInserted_eq :
      (original domain).rename (Renaming.comp Renaming.shift Renaming.shift) =
        weakenBy (original domain) 2 := by
    simp only [weakenBy, Term.rename_comp]
  have primedDomainInserted_eq :
      (weakenBy (primed domain) 1).rename
          (Renaming.lift (Renaming.comp Renaming.shift Renaming.shift)) =
        weakenBy (primed domain) 3 := by
    simp only [weakenBy, Term.rename_comp]
    apply Term.rename_congr
    funext index
    rfl
  have relationDomainInserted_eq :
      (Term.app (Term.app (weakenBy (translate domain) 2) (.var 1)) (.var 0)).rename
          (Renaming.lift (Renaming.lift
            (Renaming.comp Renaming.shift Renaming.shift))) =
        Term.app (Term.app (weakenBy (translate domain) 4) (.var 1)) (.var 0) := by
    simp only [Term.rename, weakenBy, Term.rename_comp]
    apply congrArg₂ Term.app
    · apply congrArg₂ Term.app
      · apply Term.rename_congr
        funext index
        rfl
      · rfl
    · rfl
  have codomainInserted_eq :
      (translate codomain).rename
          (Renaming.lift (Renaming.lift (Renaming.lift
            (Renaming.comp Renaming.shift Renaming.shift)))) =
        (translate codomain).rename insertTwoAfterThree := by
    apply Term.rename_congr
    funext index
    refine Fin.cases rfl ?_ index
    intro index
    refine Fin.cases rfl ?_ index
    intro index
    refine Fin.cases rfl ?_ index
    intro older
    rfl
  have productLevel_eq :
      max domainLevel (max domainLevel (max domainLevel codomainLevel)) =
        max domainLevel codomainLevel := by
    omega
  rw [productLevel_eq] at originalProductBody
  simpa only [piRelationBody, originalDomainInserted_eq,
    primedDomainInserted_eq, relationDomainInserted_eq, codomainInserted_eq,
    max_self, Nat.max_assoc] using originalProductBody

/-- Product translation preserves witness typing from the domain and codomain witnesses. -/
theorem translate_pi_witness_hasType {source : Context n}
    {domain : Term n} {codomain : Term (n + 1)} {domainLevel codomainLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped : HasType source domain (.sort domainLevel))
    (codomainWellTyped :
      HasType (ccωctx!{ %{source}, x : %{domain} }) codomain (.sort codomainLevel))
    (domainWitness :
      HasType (context source) (translate domain)
        (relatedTermType domain (.sort domainLevel)))
    (codomainWitness :
      HasType (context (ccωctx!{ %{source}, x : %{domain} })) (translate codomain)
        (relatedTermType codomain (.sort codomainLevel))) :
    HasType (context source)
      (translate (ccω!{ Π x : %{domain}, %{codomain} }))
      (relatedTermType (ccω!{ Π x : %{domain}, %{codomain} })
        (.sort (max domainLevel codomainLevel))) := by
  have productWellTyped := HasType.pi domainWellTyped codomainWellTyped
  have originalProduct := HasType.original productWellTyped translatedWellFormed
  have firstWellFormed := WellFormed.extend translatedWellFormed originalProduct
  have primedProduct := HasType.primed productWellTyped translatedWellFormed
  have primedProductWeakened := primedProduct.weaken firstWellFormed
  have bodyWellTyped := piRelationBody_hasType translatedWellFormed
    domainWellTyped codomainWellTyped domainWitness codomainWitness
  have translatedProductNormal := HasType.lam originalProduct
    (HasType.lam
      (by simpa only [weakenBy, primed, Term.rename] using primedProductWeakened)
      bodyWellTyped)
  have translatedProductNormal' :
      HasType (context source)
        (translate (ccω!{ Π x : %{domain}, %{codomain} }))
        (elementRelationType (ccω!{ Π x : %{domain}, %{codomain} })
          (max domainLevel codomainLevel)) := by
    simpa only [translate_pi_body, elementRelationType] using translatedProductNormal
  exact .conversion translatedProductNormal'
    (relatedType_hasType translatedWellFormed productWellTyped)
    (relatedTermType_sort_beta (.pi domain codomain)
      (max domainLevel codomainLevel)).symm

/-- Lambda translation preserves witness typing once the product type and body translations are typed. -/
theorem translate_lam_witness_hasType_of_productWitness {source : Context n}
    {domain : Term n} {body codomain : Term (n + 1)} {domainLevel typeLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped : HasType source domain (.sort domainLevel))
    (bodyWellTyped :
      HasType (ccωctx!{ %{source}, x : %{domain} }) body codomain)
    (productWellTyped :
      HasType source (ccω!{ Π x : %{domain}, %{codomain} }) (.sort typeLevel))
    (productWitness :
      HasType (context source)
        (translate (ccω!{ Π x : %{domain}, %{codomain} }))
        (relatedTermType (ccω!{ Π x : %{domain}, %{codomain} }) (.sort typeLevel)))
    (bodyWitness :
      HasType (context (ccωctx!{ %{source}, x : %{domain} })) (translate body)
        (relatedTermType body codomain)) :
    HasType (context source) (translate (ccω!{ λ x : %{domain}, %{body} }))
      (relatedTermType (ccω!{ λ x : %{domain}, %{body} })
        (ccω!{ Π x : %{domain}, %{codomain} })) := by
  let function : Term n := ccω!{ λ x : %{domain}, %{body} }
  have functionWellTyped :
      HasType source function (ccω!{ Π x : %{domain}, %{codomain} }) :=
    .lam domainWellTyped bodyWellTyped
  obtain ⟨fiberLevel, fiberWellTyped⟩ :=
    piRelationFiber_hasType_of_productTranslation translatedWellFormed
      functionWellTyped productWitness
  rw [piRelationFiber_eq_normal] at fiberWellTyped
  obtain ⟨_, _, originalDomainWellTyped, secondProductWellTyped⟩ :=
    fiberWellTyped.piComponents
  obtain ⟨_, _, primedDomainWellTyped, thirdProductWellTyped⟩ :=
    secondProductWellTyped.piComponents
  obtain ⟨_, outputLevel, domainRelationWellTyped, outputRelationWellTyped⟩ :=
    thirdProductWellTyped.piComponents
  change HasType (context (ccωctx!{ %{source}, x : %{domain} }))
    (applicationRelationBody function codomain) (.sort outputLevel) at outputRelationWellTyped
  have bodyWitnessExpanded :
      HasType (context (ccωctx!{ %{source}, x : %{domain} })) (translate body)
        (applicationRelationBody function codomain) :=
    .conversion bodyWitness outputRelationWellTyped
      (lambdaRelationBody_beta domain body codomain).symm
  have translatedLambdaNormal :
      HasType (context source) (translate function)
        (piRelationFiberNormal domain codomain function) := by
    change HasType (context source)
      (ccω!{
        λ x0 : %{original domain},
        λ x1 : %{weakenBy (primed domain) 1},
        λ xR : %{weakenBy (translate domain) 2} x0 x1,
        %{translate body} })
      (piRelationFiberNormal domain codomain function)
    exact .lam originalDomainWellTyped
      (.lam primedDomainWellTyped (.lam domainRelationWellTyped bodyWitnessExpanded))
  have productTranslationNormal := translate_type_hasType_normal
    translatedWellFormed productWellTyped productWitness
  have productAppliedOriginal := HasType.app productTranslationNormal
    (HasType.original functionWellTyped translatedWellFormed)
  have primedProductInstantiated :
      (weakenBy (primed (.pi domain codomain)) 1).substitute
          (Substitution.single (original function)) =
        primed (.pi domain codomain) := by
    simpa only [weakenBy] using substitute_single_rename_shift
      (primed (.pi domain codomain)) (original function)
  simp only [Term.instantiate, Term.substitute] at productAppliedOriginal
  rw [primedProductInstantiated] at productAppliedOriginal
  have relatedFunctionTypeRaw := HasType.app productAppliedOriginal
    (HasType.primed functionWellTyped translatedWellFormed)
  have relatedFunctionTypeWellTyped :
      HasType (context source)
        (relatedTermType function (ccω!{ Π x : %{domain}, %{codomain} }))
        (.sort typeLevel) := by
    simpa only [elementRelationType, relatedTermType, function, Term.instantiate,
      Term.substitute, Substitution.single, weakenBy, substitute_single_rename_shift]
      using relatedFunctionTypeRaw
  have fiberConversion := (relatedTermType_pi_beta function domain codomain).symm
  rw [piRelationFiber_eq_normal] at fiberConversion
  exact .conversion translatedLambdaNormal relatedFunctionTypeWellTyped fiberConversion

/-- The universe constructor satisfies the witness-typing conclusion in any translated context. -/
theorem translate_sort_witness_hasType {source : Context n}
    (translatedWellFormed : WellFormed (context source)) (level : Nat) :
    HasType (context source) (translate (.sort level : Term n))
      (relatedTermType (.sort level) (.sort (level + 1))) := by
  simpa only [relatedTermType, translatedSortType, original, primed, Term.rename] using
    translate_sort_hasType (n := n) (context := context source) translatedWellFormed level

/-- A translated source variable is typed by the relation recorded in its context triple. -/
theorem translate_var_witness_hasType {source : Context n}
    (translatedWellFormed : WellFormed (context source)) (index : Fin n) :
    HasType (context source) (translate (.var index))
      (relatedTermType (.var index) (source.lookup index)) := by
  have witnessVariable :=
    HasType.var translatedWellFormed (witnessRenaming n index)
  rw [context_lookup_witness source index] at witnessVariable
  simpa only [translate_var] using witnessVariable

example (source : Context n) (index : Fin n) :
    (context source).lookup (originalRenaming n index) =
      (source.lookup index).rename (originalRenaming n) :=
  context_lookup_original source index

example (source : Context n) (translatedWellFormed : WellFormed (context source)) :
    TypedRenaming source (context source) (primedRenaming n) :=
  primedTypedRenaming source translatedWellFormed

example {source : Context n} {domain : Term n} {codomain : Term (n + 1)}
    {domainLevel codomainLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped : HasType source domain (.sort domainLevel))
    (codomainWellTyped :
      HasType (ccωctx!{ %{source}, x : %{domain} }) codomain (.sort codomainLevel))
    (domainWitness :
      HasType (context source) (translate domain)
        (relatedTermType domain (.sort domainLevel)))
    (codomainWitness :
      HasType (context (ccωctx!{ %{source}, x : %{domain} })) (translate codomain)
        (relatedTermType codomain (.sort codomainLevel))) :
    HasType (context source)
      (translate (ccω!{ Π x : %{domain}, %{codomain} }))
      (relatedTermType (ccω!{ Π x : %{domain}, %{codomain} })
        (.sort (max domainLevel codomainLevel))) :=
  translate_pi_witness_hasType translatedWellFormed domainWellTyped
    codomainWellTyped domainWitness codomainWitness

example {source : Context n} {domain : Term n} {body codomain : Term (n + 1)}
    {domainLevel typeLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped : HasType source domain (.sort domainLevel))
    (bodyWellTyped :
      HasType (ccωctx!{ %{source}, x : %{domain} }) body codomain)
    (productWellTyped :
      HasType source (ccω!{ Π x : %{domain}, %{codomain} }) (.sort typeLevel))
    (productWitness :
      HasType (context source)
        (translate (ccω!{ Π x : %{domain}, %{codomain} }))
        (relatedTermType (ccω!{ Π x : %{domain}, %{codomain} }) (.sort typeLevel)))
    (bodyWitness :
      HasType (context (ccωctx!{ %{source}, x : %{domain} })) (translate body)
        (relatedTermType body codomain)) :
    HasType (context source) (translate (ccω!{ λ x : %{domain}, %{body} }))
      (relatedTermType (ccω!{ λ x : %{domain}, %{body} })
        (ccω!{ Π x : %{domain}, %{codomain} })) :=
  translate_lam_witness_hasType_of_productWitness translatedWellFormed
    domainWellTyped bodyWellTyped productWellTyped productWitness bodyWitness

end DeepWiki.Refine.DependentCalculus.RawParametricity
