import DeepWiki.Refine.Parametricity.Raw.FormationTyping
import DeepWiki.Refine.Parametricity.Univalent.RelationalCumulativity

/-! # Univalent parametricity abstraction

The formation-explicit fundamental lemma yields the full dependent abstraction theorem. -/

namespace DeepWiki.Refine.DependentCalculus.UnivalentParametricity

/-- The three displayed typing conclusions of univalent abstraction. -/
def AbstractionConclusion
    (source : DependentCalculus.Context n)
    (term type : CoreTerm n) : Prop :=
  HasType (context source) (original term) (original type) ∧
    HasType (context source) (primed term) (primed type) ∧
      HasType (context source) (termTranslation term) (relatedTermType term type)

/-- The displayed univalent abstraction statement. -/
def DisplayedAbstractionClaim : Prop :=
  ∀ {n : Nat} {source : DependentCalculus.Context n}
    {term type : CoreTerm n},
    DependentCalculus.HasType source term type →
      AbstractionConclusion source term type

/-- Univalent abstraction together with formation of the translated context. -/
def AbstractionClaim : Prop :=
  ∀ {n : Nat} {source : DependentCalculus.Context n}
    {term type : CoreTerm n},
    DependentCalculus.HasType source term type →
      WellFormed (context source) ∧ AbstractionConclusion source term type

/-- The structural induction combines translated-context formation with witness typing. -/
def StructuralAbstractionClaim : Prop :=
  ∀ {n : Nat} {source : DependentCalculus.Context n}
    {term type : CoreTerm n},
    DependentCalculus.HasType source term type →
      WellFormed (context source) ∧
        HasType (context source) (termTranslation term) (relatedTermType term type)

/-- A translated type witness gives its direct endpoint package typing. -/
theorem termTranslation_typePackage_hasType
    {source : DependentCalculus.Context n}
    {type : CoreTerm n} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (typeWellTyped :
      DependentCalculus.HasType source type (.sort level))
    (typeWitness :
      HasType (context source) (termTranslation type)
        (relatedTermType type (.sort level))) :
    HasType (context source) (termTranslation type)
      (Term.packageType level (original type) (primed type)) := by
  exact .conversion typeWitness
    (packageType_hasType translatedWellFormed
      (HasType.original typeWellTyped translatedWellFormed)
      (HasType.primed typeWellTyped translatedWellFormed))
    (relatedTermType_sort_convertible type level)

/-- A translated type witness makes every corresponding relation fiber universe-typed. -/
theorem relatedTermType_hasType_of_typeWitness
    {source : DependentCalculus.Context n}
    {term type : CoreTerm n} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (termWellTyped :
      DependentCalculus.HasType source term type)
    (typeWellTyped :
      DependentCalculus.HasType source type (.sort level))
    (typeWitness :
      HasType (context source) (termTranslation type)
        (relatedTermType type (.sort level))) :
    HasType (context source) (relatedTermType term type) (.sort level) := by
  have package := termTranslation_typePackage_hasType translatedWellFormed
    typeWellTyped typeWitness
  have originalTerm := HasType.original termWellTyped translatedWellFormed
  have primedTerm := HasType.primed termWellTyped translatedWellFormed
  have originalType := HasType.original typeWellTyped translatedWellFormed
  have primedType := HasType.primed typeWellTyped translatedWellFormed
  have projected := HasType.relationProjection originalType primedType package
  have appliedOriginal := HasType.app projected originalTerm
  have primedTypeInstantiated :
      ((primed type).rename
          DependentCalculus.Renaming.shift).substitute
          (Substitution.single (original term)) = primed type := by
    change ((primed type).rename
        DependentCalculus.Renaming.shift).instantiate
      (original term) = primed type
    exact Term.instantiate_rename_shift _ _
  have appliedOriginal' :
      HasType (context source)
        (.app (Term.rel (termTranslation type)) (original term))
        (.pi (primed type) (.sort level)) := by
    simpa only [Term.relationType, Term.instantiate, Term.substitute,
      primedTypeInstantiated] using appliedOriginal
  have appliedPrimed := HasType.app appliedOriginal' primedTerm
  simpa only [relatedTermType, typeTranslation, Term.rel,
    Term.relationApplication, Term.relationType, Term.instantiate,
    Term.substitute, Term.rename, Term.instantiate_rename_shift] using appliedPrimed

/-- Package typing forms the endpoint-and-relation context. -/
theorem relationalExtend_wellFormed
    {base : Context n} {left right package : Term n} {level : Nat}
    (baseWellFormed : WellFormed base)
    (leftWellTyped : HasType base left (.sort level))
    (rightWellTyped : HasType base right (.sort level))
    (packageWellTyped :
      HasType base package (Term.packageType level left right)) :
    WellFormed (relationalExtend base left right package) ∧
      HasType
        (.extend (.extend base left)
          (right.rename DependentCalculus.Renaming.shift))
        (Term.relatedDomain package) (.sort level) := by
  let leftContext : Context (n + 1) := .extend base left
  have leftContextWellFormed : WellFormed leftContext :=
    .extend baseWellFormed leftWellTyped
  have weakenedRight :
      HasType leftContext
        (right.rename DependentCalculus.Renaming.shift)
        (.sort level) := by
    simpa only [leftContext, Term.rename] using
      rightWellTyped.weaken leftContextWellFormed
  let endpointContext : Context (n + 2) :=
    .extend leftContext
      (right.rename DependentCalculus.Renaming.shift)
  have endpointContextWellFormed : WellFormed endpointContext :=
    .extend leftContextWellFormed weakenedRight
  have weakenedPackageOnce := packageWellTyped.weaken leftContextWellFormed
  have weakenedPackageTwice := weakenedPackageOnce.weaken endpointContextWellFormed
  have weakenedPackage :
      HasType endpointContext (package.weakenBy 2)
        (Term.packageType level (left.weakenBy 2) (right.weakenBy 2)) := by
    simpa only [endpointContext, leftContext, Term.weakenBy, Term.rename,
      Term.packageType_rename] using weakenedPackageTwice
  have weakenedLeftOnce := leftWellTyped.weaken leftContextWellFormed
  have weakenedLeftTwice := weakenedLeftOnce.weaken endpointContextWellFormed
  have weakenedLeft :
      HasType endpointContext (left.weakenBy 2) (.sort level) := by
    simpa only [endpointContext, leftContext, Term.weakenBy, Term.rename] using
      weakenedLeftTwice
  have weakenedRightOnce := rightWellTyped.weaken leftContextWellFormed
  have weakenedRightTwice := weakenedRightOnce.weaken endpointContextWellFormed
  have weakenedRight :
      HasType endpointContext (right.weakenBy 2) (.sort level) := by
    simpa only [endpointContext, leftContext, Term.weakenBy, Term.rename] using
      weakenedRightTwice
  have leftVariable :
      HasType endpointContext (.var 1) (left.weakenBy 2) := by
    have variableWellTyped :=
      HasType.var endpointContextWellFormed (1 : Fin (n + 2))
    change HasType endpointContext (.var 1)
      ((left.rename DependentCalculus.Renaming.shift).rename
        DependentCalculus.Renaming.shift) at variableWellTyped
    simpa only [Term.weakenBy] using variableWellTyped
  have rightVariable :
      HasType endpointContext (.var 0) (right.weakenBy 2) := by
    have variableWellTyped :=
      HasType.var endpointContextWellFormed (0 : Fin (n + 2))
    change HasType endpointContext (.var 0)
      ((right.rename DependentCalculus.Renaming.shift).rename
        DependentCalculus.Renaming.shift) at variableWellTyped
    simpa only [Term.weakenBy] using variableWellTyped
  have projected :=
    HasType.relationProjection weakenedLeft weakenedRight weakenedPackage
  have appliedLeft := HasType.app projected leftVariable
  have appliedLeft' :
      HasType endpointContext
        (.app (Term.rel (package.weakenBy 2)) (.var 1))
        (.pi (right.weakenBy 2) (.sort level)) := by
    change HasType endpointContext
      (.app (Term.rel (package.weakenBy 2)) (.var 1))
      (.pi (((right.weakenBy 2).rename
        DependentCalculus.Renaming.shift).instantiate (.var 1))
        (.sort level)) at appliedLeft
    rw [Term.instantiate_rename_shift] at appliedLeft
    exact appliedLeft
  have appliedRight := HasType.app appliedLeft' rightVariable
  have relatedDomainWellTyped :
      HasType endpointContext (Term.relatedDomain package) (.sort level) := by
    simpa only [Term.relatedDomain, Term.relationApplication, Term.rel,
      Term.instantiate, Term.substitute, Term.rename] using appliedRight
  exact ⟨by
    simpa only [relationalExtend, endpointContext, leftContext] using
      WellFormed.extend endpointContextWellFormed relatedDomainWellTyped,
    by simpa only [endpointContext, leftContext] using relatedDomainWellTyped⟩

/-- The original endpoint context embeds into its relational extension. -/
theorem originalBinderTypedRenaming
    {base : Context n} {left right package : Term n}
    (extendedWellFormed : WellFormed (relationalExtend base left right package)) :
    TypedRenaming (.extend base left) (relationalExtend base left right package)
      originalBinderRenaming where
  targetWellFormed := extendedWellFormed
  lookup_eq index := by
    refine Fin.cases ?_ ?_ index
    · simp [relationalExtend, originalBinderRenaming, Context.lookup]
      simp only [Term.rename_comp]
      apply Term.rename_congr
      funext element
      rfl
    · intro older
      simp [relationalExtend, originalBinderRenaming, Context.lookup]
      simp only [Term.rename_comp]
      apply Term.rename_congr
      funext element
      rfl

/-- The primed endpoint context embeds into its relational extension. -/
theorem primedBinderTypedRenaming
    {base : Context n} {left right package : Term n}
    (extendedWellFormed : WellFormed (relationalExtend base left right package)) :
    TypedRenaming (.extend base right) (relationalExtend base left right package)
      primedBinderRenaming where
  targetWellFormed := extendedWellFormed
  lookup_eq index := by
    refine Fin.cases ?_ ?_ index
    · simp [relationalExtend, primedBinderRenaming, Context.lookup]
      simp only [Term.rename_comp]
      apply Term.rename_congr
      funext element
      rfl
    · intro older
      simp [relationalExtend, primedBinderRenaming, Context.lookup]
      simp only [Term.rename_comp]
      apply Term.rename_congr
      funext element
      rfl

/-- A domain witness forms its translated source extension. -/
theorem context_extend_wellFormed
    {source : DependentCalculus.Context n}
    {domain : CoreTerm n} {domainLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped :
      DependentCalculus.HasType source domain (.sort domainLevel))
    (domainWitness :
      HasType (context source) (termTranslation domain)
        (relatedTermType domain (.sort domainLevel))) :
    WellFormed (context (.extend source domain)) ∧
      HasType
        (.extend (.extend (context source) (original domain))
          ((primed domain).weakenBy 1))
        (Term.relatedDomain (termTranslation domain)) (.sort domainLevel) := by
  have originalDomain := HasType.original domainWellTyped translatedWellFormed
  have primedDomain := HasType.primed domainWellTyped translatedWellFormed
  have domainPackage := termTranslation_typePackage_hasType translatedWellFormed
    domainWellTyped domainWitness
  have formed := relationalExtend_wellFormed translatedWellFormed
    originalDomain primedDomain domainPackage
  exact ⟨by
    rw [context_extend_eq_relationalExtend]
    exact formed.1,
    formed.2⟩

/-- Original codomain embedding preserves typing in the original endpoint context. -/
theorem originalCodomain_hasType
    {source : DependentCalculus.Context n}
    {domain : CoreTerm n} {codomain : CoreTerm (n + 1)} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped :
      DependentCalculus.HasType source domain (.sort level))
    {codomainLevel : Nat}
    (codomainWellTyped :
      DependentCalculus.HasType (.extend source domain)
        codomain (.sort codomainLevel)) :
    HasType (.extend (context source) (original domain))
      (originalCodomain codomain) (.sort codomainLevel) := by
  have baseRenaming := originalTypedRenaming source translatedWellFormed
  have embeddedDomain := HasType.ofCore domainWellTyped
  have renamedDomain := embeddedDomain.rename baseRenaming
  have lifted := baseRenaming.lift renamedDomain
  have renamed := (HasType.ofCore codomainWellTyped).rename lifted
  simpa only [original, originalCodomain, RawParametricity.original,
    DependentCalculus.Term.rename, Term.ofCore_rename,
    Term.ofCore, Term.rename] using renamed

/-- Primed codomain embedding preserves typing in the primed endpoint context. -/
theorem primedCodomain_hasType
    {source : DependentCalculus.Context n}
    {domain : CoreTerm n} {codomain : CoreTerm (n + 1)} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped :
      DependentCalculus.HasType source domain (.sort level))
    {codomainLevel : Nat}
    (codomainWellTyped :
      DependentCalculus.HasType (.extend source domain)
        codomain (.sort codomainLevel)) :
    HasType (.extend (context source) (primed domain))
      (primedCodomain codomain) (.sort codomainLevel) := by
  have baseRenaming := primedTypedRenaming source translatedWellFormed
  have embeddedDomain := HasType.ofCore domainWellTyped
  have renamedDomain := embeddedDomain.rename baseRenaming
  have lifted := baseRenaming.lift renamedDomain
  have renamed := (HasType.ofCore codomainWellTyped).rename lifted
  simpa only [primed, primedCodomain, RawParametricity.primed,
    DependentCalculus.Term.rename, Term.ofCore_rename,
    Term.ofCore, Term.rename] using renamed

/-- The translated dependent product satisfies the univalent witness conclusion. -/
theorem termTranslation_pi_witness_hasType
    {source : DependentCalculus.Context n}
    {domain : CoreTerm n} {codomain : CoreTerm (n + 1)}
    {domainLevel codomainLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped :
      DependentCalculus.HasType source domain (.sort domainLevel))
    (codomainWellTyped :
      DependentCalculus.HasType (.extend source domain)
        codomain (.sort codomainLevel))
    (codomainTranslatedWellFormed : WellFormed (context (.extend source domain)))
    (domainWitness :
      HasType (context source) (termTranslation domain)
        (relatedTermType domain (.sort domainLevel)))
    (codomainWitness :
      HasType (context (.extend source domain)) (termTranslation codomain)
        (relatedTermType codomain (.sort codomainLevel))) :
    HasType (context source) (termTranslation (.pi domain codomain))
      (relatedTermType (.pi domain codomain)
        (.sort (max domainLevel codomainLevel))) := by
  have originalDomain := HasType.original domainWellTyped translatedWellFormed
  have primedDomain := HasType.primed domainWellTyped translatedWellFormed
  have originalCodomain := originalCodomain_hasType translatedWellFormed
    domainWellTyped codomainWellTyped
  have primedCodomain := primedCodomain_hasType translatedWellFormed
    domainWellTyped codomainWellTyped
  have domainPackage := termTranslation_typePackage_hasType translatedWellFormed
    domainWellTyped domainWitness
  have codomainPackageNormal :=
    termTranslation_typePackage_hasType codomainTranslatedWellFormed
      codomainWellTyped codomainWitness
  have codomainPackage :
      HasType
        (relationalExtend (context source) (original domain) (primed domain)
          (termTranslation domain))
        (termTranslation codomain)
        (Term.packageType codomainLevel
          ((UnivalentParametricity.originalCodomain codomain).rename
            originalBinderRenaming)
          ((UnivalentParametricity.primedCodomain codomain).rename
            primedBinderRenaming)) := by
    rw [← context_extend_eq_relationalExtend]
    rw [← original_eq_originalCodomain_rename,
      ← primed_eq_primedCodomain_rename]
    exact codomainPackageNormal
  have packageTyping := HasType.dependentProductPackage
    originalDomain primedDomain originalCodomain primedCodomain
    domainPackage codomainPackage
  have originalProduct :=
    HasType.original
      (DependentCalculus.HasType.pi domainWellTyped codomainWellTyped)
      translatedWellFormed
  have primedProduct :=
    HasType.primed
      (DependentCalculus.HasType.pi domainWellTyped codomainWellTyped)
      translatedWellFormed
  have targetTypeWellTyped := relatedTermType_sort_hasType translatedWellFormed
    originalProduct primedProduct
  have translatedProductPackage :
      HasType (context source) (termTranslation (.pi domain codomain))
        (Term.packageType (max domainLevel codomainLevel)
          (original (.pi domain codomain)) (primed (.pi domain codomain))) := by
    simpa only [termTranslation_pi, original, primed,
      RawParametricity.original, RawParametricity.primed,
      DependentCalculus.Term.rename, Term.ofCore,
      UnivalentParametricity.originalCodomain,
      UnivalentParametricity.primedCodomain] using packageTyping
  exact .conversion translatedProductPackage targetTypeWellTyped
    (relatedTermType_sort_convertible (.pi domain codomain)
      (max domainLevel codomainLevel)).symm

/-- A dependent function applied to the newest source variable has its codomain. -/
theorem fiberApplication_hasType
    {source : DependentCalculus.Context n}
    {function domain : CoreTerm n} {codomain : CoreTerm (n + 1)}
    (functionWellTyped :
      DependentCalculus.HasType source function (.pi domain codomain))
    (extendedWellFormed :
      DependentCalculus.WellFormed (.extend source domain)) :
    DependentCalculus.HasType (.extend source domain)
      (fiberApplication function) codomain := by
  have weakenedFunction := functionWellTyped.weaken extendedWellFormed
  have newestVariable :=
    DependentCalculus.HasType.var extendedWellFormed
      (0 : Fin (n + 1))
  have application :=
    DependentCalculus.HasType.app weakenedFunction newestVariable
  have codomainInstantiated :
      (codomain.rename
          (DependentCalculus.Renaming.lift
            DependentCalculus.Renaming.shift)).instantiate
        (.var 0) = codomain := by
    unfold DependentCalculus.Term.instantiate
    rw [DependentCalculus.Term.substitute_rename]
    rw [show
      (fun index =>
        DependentCalculus.Substitution.single (.var 0)
          (DependentCalculus.Renaming.lift
            DependentCalculus.Renaming.shift index)) =
        DependentCalculus.Substitution.identity by
      funext index
      refine Fin.cases rfl ?_ index
      intro older
      rfl]
    exact DependentCalculus.Term.substitute_identity codomain
  rw [codomainInstantiated] at application
  simpa only [fiberApplication] using application

/-- The normalized projected product fiber is universe-typed. -/
theorem piRelationFiberNormal_hasType
    {source : DependentCalculus.Context n}
    {function domain : CoreTerm n} {codomain : CoreTerm (n + 1)}
    {domainLevel codomainLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (functionWellTyped :
      DependentCalculus.HasType source function (.pi domain codomain))
    (domainWellTyped :
      DependentCalculus.HasType source domain (.sort domainLevel))
    (codomainWellTyped :
      DependentCalculus.HasType (.extend source domain)
        codomain (.sort codomainLevel))
    (domainWitness :
      HasType (context source) (termTranslation domain)
        (relatedTermType domain (.sort domainLevel)))
    (codomainWitness :
      HasType (context (.extend source domain)) (termTranslation codomain)
        (relatedTermType codomain (.sort codomainLevel))) :
    HasType (context source) (piRelationFiberNormal domain codomain function)
      (.sort (max domainLevel codomainLevel)) := by
  have originalDomain :
      HasType (context source) (original domain) (.sort domainLevel) := by
    simpa only [original, RawParametricity.original,
      DependentCalculus.Term.rename, Term.ofCore] using
      HasType.original domainWellTyped translatedWellFormed
  have firstWellFormed : WellFormed (.extend (context source) (original domain)) :=
    .extend translatedWellFormed originalDomain
  have primedDomainBase :
      HasType (context source) (primed domain) (.sort domainLevel) := by
    simpa only [primed, RawParametricity.primed,
      DependentCalculus.Term.rename, Term.ofCore] using
      HasType.primed domainWellTyped translatedWellFormed
  have primedDomain :
      HasType (.extend (context source) (original domain))
        ((primed domain).weakenBy 1) (.sort domainLevel) := by
    simpa only [Term.weakenBy, Term.rename] using
      primedDomainBase.weaken firstWellFormed
  have extension := context_extend_wellFormed translatedWellFormed
    domainWellTyped domainWitness
  have relatedDomain := extension.2
  have fiberWellTyped := fiberApplication_hasType functionWellTyped
    codomainWellTyped.contextWellFormed
  have outputWellTyped := relatedTermType_hasType_of_typeWitness extension.1
    fiberWellTyped codomainWellTyped codomainWitness
  rw [relatedTermType_fiberApplication] at outputWellTyped
  have relationProduct := HasType.pi relatedDomain outputWellTyped
  have primedProduct := HasType.pi primedDomain relationProduct
  have originalProduct := HasType.pi originalDomain primedProduct
  have levelEquality :
      max domainLevel (max domainLevel (max domainLevel codomainLevel)) =
        max domainLevel codomainLevel := by
    omega
  rw [levelEquality] at originalProduct
  simpa only [piRelationFiberNormal] using originalProduct

/-- A function witness alone exposes a universe-typed normalized product fiber. -/
theorem piRelationFiberNormal_hasType_of_functionWitness
    {source : DependentCalculus.Context n}
    {function domain : CoreTerm n} {codomain : CoreTerm (n + 1)}
    (translatedWellFormed : WellFormed (context source))
    (functionWellTyped :
      DependentCalculus.HasType source function (.pi domain codomain))
    (functionWitness :
      HasType (context source) (termTranslation function)
        (relatedTermType function (.pi domain codomain))) :
    ∃ level, HasType (context source)
      (piRelationFiberNormal domain codomain function) (.sort level) := by
  obtain ⟨witnessLevel, witnessTypeWellTyped⟩ := functionWitness.typeWellTyped
  change HasType (context source)
    (.app
      (.app (.relationProjection (termTranslation (.pi domain codomain)))
        (original function))
      (primed function)) (.sort witnessLevel) at witnessTypeWellTyped
  obtain ⟨_, _, firstApplicationWellTyped, _⟩ :=
    witnessTypeWellTyped.appComponents
  obtain ⟨_, _, projectionWellTyped, _⟩ :=
    firstApplicationWellTyped.appComponents
  obtain ⟨_, _, _, _, _, productPackageWellTyped⟩ :=
    projectionWellTyped.relationProjectionComponents
  rw [termTranslation_pi] at productPackageWellTyped
  obtain ⟨domainLevel, codomainLevel, originalDomain, primedDomain,
      originalCodomain, primedCodomain, domainPackage, codomainPackage⟩ :=
    productPackageWellTyped.dependentProductPackageComponents
  have extension := relationalExtend_wellFormed translatedWellFormed
    originalDomain primedDomain domainPackage
  have originalCodomain' :=
    originalCodomain.rename (originalBinderTypedRenaming extension.1)
  have primedCodomain' :=
    primedCodomain.rename (primedBinderTypedRenaming extension.1)
  have projectedCodomain := HasType.relationProjection
    originalCodomain' primedCodomain' codomainPackage
  obtain ⟨_, functionTypeWellTyped⟩ := functionWellTyped.typeWellTyped
  obtain ⟨_, _, _, codomainCoreWellTyped⟩ :=
    functionTypeWellTyped.piComponents
  have fiberCoreWellTyped := fiberApplication_hasType functionWellTyped
    codomainCoreWellTyped.contextWellFormed
  have translatedExtensionWellFormed :
      WellFormed (context (.extend source domain)) := by
    rw [context_extend_eq_relationalExtend]
    exact extension.1
  have originalFiber :=
    HasType.original fiberCoreWellTyped translatedExtensionWellFormed
  have primedFiber :=
    HasType.primed fiberCoreWellTyped translatedExtensionWellFormed
  rw [context_extend_eq_relationalExtend] at originalFiber primedFiber
  have originalFiber' :
      HasType
        (relationalExtend (context source) (original domain) (primed domain)
          (termTranslation domain))
        (original (fiberApplication function))
        ((UnivalentParametricity.originalCodomain codomain).rename
          originalBinderRenaming) := by
    simpa only [scopeSize, RawParametricity.scopeSize,
      original_eq_originalCodomain_rename codomain] using originalFiber
  have primedFiber' :
      HasType
        (relationalExtend (context source) (original domain) (primed domain)
          (termTranslation domain))
        (primed (fiberApplication function))
        ((UnivalentParametricity.primedCodomain codomain).rename
          primedBinderRenaming) := by
    simpa only [scopeSize, RawParametricity.scopeSize,
      primed_eq_primedCodomain_rename codomain] using primedFiber
  have outputWellTyped := relationApplication_hasType projectedCodomain
    originalFiber' primedFiber'
  have outputWellTyped' :
      HasType (context (.extend source domain))
        (relatedTermType (fiberApplication function) codomain)
        (.sort codomainLevel) := by
    rw [context_extend_eq_relationalExtend]
    simpa only [scopeSize, RawParametricity.scopeSize, relatedTermType,
      typeTranslation, Term.rel] using outputWellTyped
  rw [relatedTermType_fiberApplication] at outputWellTyped'
  have firstWellFormed :
      WellFormed (.extend (context source) (original domain)) :=
    .extend translatedWellFormed originalDomain
  have primedDomain' :
      HasType (.extend (context source) (original domain))
        ((primed domain).weakenBy 1) (.sort domainLevel) := by
    simpa only [Term.weakenBy, Term.rename] using
      primedDomain.weaken firstWellFormed
  have relationProduct := HasType.pi extension.2 outputWellTyped'
  have primedProduct := HasType.pi primedDomain' relationProduct
  have originalProduct := HasType.pi originalDomain primedProduct
  exact ⟨_, by simpa only [piRelationFiberNormal] using originalProduct⟩

/-- The simultaneous substitution for an argument's original, primed, and witness copies. -/
def argumentTripleSubstitution (argument : CoreTerm n) :
    Substitution (scopeSize n + 3) (scopeSize n) :=
  (relationalSingle argument).relational

/-- Argument-triple substitution sends the witness slot to the translated argument. -/
@[simp] theorem argumentTripleSubstitution_zero (argument : CoreTerm n) :
    argumentTripleSubstitution argument 0 = termTranslation argument :=
  rfl

/-- Argument-triple substitution sends the primed slot to the primed argument. -/
@[simp] theorem argumentTripleSubstitution_one (argument : CoreTerm n) :
    argumentTripleSubstitution argument 1 = primed argument :=
  rfl

/-- Argument-triple substitution sends the original slot to the original argument. -/
@[simp] theorem argumentTripleSubstitution_two (argument : CoreTerm n) :
    argumentTripleSubstitution argument 2 = original argument :=
  rfl

/-- Argument-triple substitution cancels three ambient weakenings. -/
theorem substitute_argumentTriple_weakenBy_three
    (term : Term (scopeSize n)) (argument : CoreTerm n) :
    (term.weakenBy 3).substitute (argumentTripleSubstitution argument) = term := by
  change (((term.rename DependentCalculus.Renaming.shift).rename
      DependentCalculus.Renaming.shift).rename
      DependentCalculus.Renaming.shift).substitute
      (argumentTripleSubstitution argument) = term
  rw [Term.substitute_rename, Term.substitute_rename, Term.substitute_rename]
  rw [show
      (fun index => argumentTripleSubstitution argument
        (DependentCalculus.Renaming.shift
          (DependentCalculus.Renaming.shift
            (DependentCalculus.Renaming.shift index)))) =
        Substitution.identity by
    funext index
    rfl]
  exact Term.substitute_identity term

/-- Sequentially instantiating the three relation binders is argument-triple substitution. -/
theorem substitute_argumentTriple (term : Term (scopeSize n + 3))
    (argument : CoreTerm n) :
    (((term.substitute
          (Substitution.lift
            (Substitution.lift (Substitution.single (original argument))))).substitute
        (Substitution.lift (Substitution.single (primed argument)))).substitute
      (Substitution.single (termTranslation argument))) =
        term.substitute (argumentTripleSubstitution argument) := by
  rw [Term.substitute_comp, Term.substitute_comp]
  apply Term.substitute_congr
  funext index
  unfold Substitution.comp argumentTripleSubstitution relationalSingle
  refine Fin.cases rfl (fun index => ?_) index
  refine Fin.cases ?_ (fun index => ?_) index
  · change ((primed argument).rename
        DependentCalculus.Renaming.shift).substitute
      (Substitution.single (termTranslation argument)) = primed argument
    exact Term.instantiate_rename_shift _ _
  refine Fin.cases ?_ (fun _older => rfl) index
  · simp only [Substitution.lift_succ, Substitution.single_zero]
    change (((original argument).rename
        DependentCalculus.Renaming.shift).rename
        DependentCalculus.Renaming.shift).substitute
      (Substitution.comp (Substitution.single (termTranslation argument))
        (Substitution.lift (Substitution.single (primed argument)))) =
      original argument
    rw [← Term.substitute_comp, Term.substitute_rename_shift_lift]
    rw [show ((original argument).rename
          DependentCalculus.Renaming.shift).substitute
          (Substitution.single (primed argument)) = original argument by
      exact Term.instantiate_rename_shift _ _]
    exact Term.instantiate_rename_shift _ _

/-- A lifted single substitution cancels the corresponding weakened binder. -/
theorem substitute_liftBy_single_weakenBy (term : Term n) (argument : Term n)
    (amount : Nat) :
    ((term.weakenBy 1).weakenBy amount).substitute
        (Substitution.liftBy (Substitution.single argument) amount) =
      term.weakenBy amount := by
  rw [← Term.weakenBy_substitute]
  change ((term.weakenBy 1).instantiate argument).weakenBy amount = _
  rw [show term.weakenBy 1 =
      term.rename DependentCalculus.Renaming.shift from rfl,
    Term.instantiate_rename_shift]

/-- A single substitution removes a onefold weakening. -/
@[simp] theorem substitute_single_weakenBy_one (term argument : Term n) :
    (term.weakenBy 1).substitute (Substitution.single argument) = term := by
  change (term.rename DependentCalculus.Renaming.shift).instantiate
    argument = term
  exact Term.instantiate_rename_shift term argument

/-- Instantiating a projected relation domain at both endpoints gives direct application. -/
theorem relatedDomain_instantiate (package left right : Term n) :
    ((Term.relatedDomain package).substitute
        (Substitution.lift (Substitution.single left))).instantiate right =
      Term.relationApplication (Term.rel package) left right := by
  unfold Term.relatedDomain Term.relationApplication Term.rel
  simp only [Term.instantiate, Term.substitute]
  rw [show ((package.weakenBy 2).substitute
        (Substitution.lift (Substitution.single left))).substitute
        (Substitution.single right) = package by
    rw [show (package.weakenBy 2).substitute
          (Substitution.lift (Substitution.single left)) =
        package.weakenBy 1 by
      simpa only [Term.weakenBy, Substitution.liftBy] using
        substitute_liftBy_single_weakenBy package left 1]
    exact substitute_single_weakenBy_one package right]
  rw [show ((Substitution.lift (Substitution.single left) 1).substitute
        (Substitution.single right)) = left by
    exact Term.instantiate_rename_shift _ _]
  rfl

/-- Substituting an argument triple specializes a product fiber's output relation. -/
theorem applicationRelationBody_substitute
    (function argument : CoreTerm n) (codomain : CoreTerm (n + 1)) :
    (applicationRelationBody function codomain).substitute
        (argumentTripleSubstitution argument) =
      relatedTermType (.app function argument) (codomain.instantiate argument) := by
  unfold applicationRelationBody relatedTermType Term.relationApplication
  rw [show typeTranslation (codomain.instantiate argument) =
      (typeTranslation codomain).substitute (argumentTripleSubstitution argument) by
    change typeTranslation (codomain.substitute
        (DependentCalculus.Substitution.single argument)) =
      (typeTranslation codomain).substitute (relationalSingle argument).relational
    exact typeTranslation_substitute (relationalSingle argument) codomain]
  simp only [Term.substitute, substitute_argumentTriple_weakenBy_three,
    argumentTripleSubstitution_one, argumentTripleSubstitution_two, original, primed,
    RawParametricity.original, RawParametricity.primed,
    DependentCalculus.Term.rename, Term.ofCore]

/-- A well-formed product fiber lets application preserve witness typing. -/
theorem termTranslation_app_witness_hasType_of_fiber
    {source : DependentCalculus.Context n}
    {function argument domain : CoreTerm n} {codomain : CoreTerm (n + 1)}
    {fiberLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (argumentWellTyped :
      DependentCalculus.HasType source argument domain)
    (functionWitness :
      HasType (context source) (termTranslation function)
        (relatedTermType function (.pi domain codomain)))
    (argumentWitness :
      HasType (context source) (termTranslation argument)
        (relatedTermType argument domain))
    (fiberWellTyped :
      HasType (context source) (piRelationFiberNormal domain codomain function)
        (.sort fiberLevel)) :
    HasType (context source) (termTranslation (.app function argument))
      (relatedTermType (.app function argument) (codomain.instantiate argument)) := by
  have fiberConversion := relatedTermType_pi_beta function domain codomain
  rw [piRelationFiber_eq_normal] at fiberConversion
  have normalizedFunction :
      HasType (context source) (termTranslation function)
        (piRelationFiberNormal domain codomain function) :=
    .conversion functionWitness fiberWellTyped fiberConversion
  have appliedOriginal := HasType.app normalizedFunction
    (HasType.original argumentWellTyped translatedWellFormed)
  have appliedOriginal' :
      HasType (context source)
        (.app (termTranslation function) (original argument))
        (.pi (primed domain)
          (.pi
            ((Term.relatedDomain (termTranslation domain)).substitute
              (Substitution.lift (Substitution.single (original argument))))
            ((applicationRelationBody function codomain).substitute
              (Substitution.lift
                (Substitution.lift (Substitution.single (original argument))))))) := by
    simpa only [piRelationFiberNormal, Term.instantiate, Term.substitute,
      substitute_single_weakenBy_one] using appliedOriginal
  have appliedPrimed := HasType.app appliedOriginal'
    (HasType.primed argumentWellTyped translatedWellFormed)
  have appliedPrimed' :
      HasType (context source)
        (.app (.app (termTranslation function) (original argument)) (primed argument))
        (.pi (relatedTermType argument domain)
          (((applicationRelationBody function codomain).substitute
            (Substitution.lift
              (Substitution.lift (Substitution.single (original argument))))).substitute
            (Substitution.lift (Substitution.single (primed argument))))) := by
    simp only [Term.instantiate, Term.substitute] at appliedPrimed
    rw [show ((Term.relatedDomain (termTranslation domain)).substitute
        (Substitution.lift (Substitution.single (original argument)))).substitute
        (Substitution.single (primed argument)) =
      Term.relationApplication (Term.rel (termTranslation domain))
        (original argument) (primed argument) by
      simpa only [Term.instantiate] using relatedDomain_instantiate
        (termTranslation domain) (original argument) (primed argument)] at appliedPrimed
    simpa only [relatedTermType, typeTranslation, Term.rel] using appliedPrimed
  have appliedWitness := HasType.app appliedPrimed' argumentWitness
  simp only [Term.instantiate] at appliedWitness
  rw [substitute_argumentTriple, applicationRelationBody_substitute] at appliedWitness
  simpa only [termTranslation_app] using appliedWitness

/-- Application preserves the univalent witness-typing conclusion. -/
theorem termTranslation_app_witness_hasType
    {source : DependentCalculus.Context n}
    {function argument domain : CoreTerm n} {codomain : CoreTerm (n + 1)}
    {domainLevel codomainLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (functionWellTyped :
      DependentCalculus.HasType source function (.pi domain codomain))
    (argumentWellTyped :
      DependentCalculus.HasType source argument domain)
    (domainWellTyped :
      DependentCalculus.HasType source domain (.sort domainLevel))
    (codomainWellTyped :
      DependentCalculus.HasType (.extend source domain)
        codomain (.sort codomainLevel))
    (domainWitness :
      HasType (context source) (termTranslation domain)
        (relatedTermType domain (.sort domainLevel)))
    (codomainWitness :
      HasType (context (.extend source domain)) (termTranslation codomain)
        (relatedTermType codomain (.sort codomainLevel)))
    (functionWitness :
      HasType (context source) (termTranslation function)
        (relatedTermType function (.pi domain codomain)))
    (argumentWitness :
      HasType (context source) (termTranslation argument)
        (relatedTermType argument domain)) :
    HasType (context source) (termTranslation (.app function argument))
      (relatedTermType (.app function argument) (codomain.instantiate argument)) := by
  have fiberWellTyped := piRelationFiberNormal_hasType translatedWellFormed
    functionWellTyped domainWellTyped codomainWellTyped domainWitness codomainWitness
  exact termTranslation_app_witness_hasType_of_fiber translatedWellFormed
    argumentWellTyped functionWitness argumentWitness fiberWellTyped

/-- Function and argument witnesses suffice for translated application typing. -/
theorem termTranslation_app_witness_hasType_of_witnesses
    {source : DependentCalculus.Context n}
    {function argument domain : CoreTerm n} {codomain : CoreTerm (n + 1)}
    (translatedWellFormed : WellFormed (context source))
    (functionWellTyped :
      DependentCalculus.HasType source function (.pi domain codomain))
    (argumentWellTyped :
      DependentCalculus.HasType source argument domain)
    (functionWitness :
      HasType (context source) (termTranslation function)
        (relatedTermType function (.pi domain codomain)))
    (argumentWitness :
      HasType (context source) (termTranslation argument)
        (relatedTermType argument domain)) :
    HasType (context source) (termTranslation (.app function argument))
      (relatedTermType (.app function argument) (codomain.instantiate argument)) := by
  obtain ⟨_, fiberWellTyped⟩ :=
    piRelationFiberNormal_hasType_of_functionWitness translatedWellFormed
      functionWellTyped functionWitness
  exact termTranslation_app_witness_hasType_of_fiber translatedWellFormed
    argumentWellTyped functionWitness argumentWitness fiberWellTyped

/-- A triply weakened original lambda computes at the original argument slot. -/
theorem original_lam_apply_convertible (domain : CoreTerm n)
    (body : CoreTerm (n + 1)) :
    Convertible
      (.app ((original (.lam domain body)).weakenBy 3)
        (.var (2 : Fin (scopeSize n + 3))))
      (original body) := by
  convert Convertible.ofCore
      (RawParametricity.weakened_original_lam_apply_beta domain body) using 1
  all_goals simp only [scopeSize, original, Term.weakenBy,
    RawParametricity.weakenBy, Term.ofCore, Term.ofCore_rename]
  all_goals rfl

/-- A triply weakened primed lambda computes at the primed argument slot. -/
theorem primed_lam_apply_convertible (domain : CoreTerm n)
    (body : CoreTerm (n + 1)) :
    Convertible
      (.app ((primed (.lam domain body)).weakenBy 3)
        (.var (1 : Fin (scopeSize n + 3))))
      (primed body) := by
  convert Convertible.ofCore
      (RawParametricity.weakened_primed_lam_apply_beta domain body) using 1
  all_goals simp only [scopeSize, primed, Term.weakenBy,
    RawParametricity.weakenBy, Term.ofCore, Term.ofCore_rename]
  all_goals rfl

/-- The output relation for a translated lambda computes to the relation between its bodies. -/
theorem lambdaApplicationRelationBody_convertible (domain : CoreTerm n)
    (body codomain : CoreTerm (n + 1)) :
    Convertible (applicationRelationBody (.lam domain body) codomain)
      (relatedTermType body codomain) := by
  unfold applicationRelationBody relatedTermType typeTranslation
    Term.relationApplication
  have originalBeta := original_lam_apply_convertible domain body
  have primedBeta := primed_lam_apply_convertible domain body
  exact (originalBeta.appArgument.appFunction).trans primedBeta.appArgument

/-- Lambda abstraction preserves the univalent witness-typing conclusion. -/
theorem termTranslation_lam_witness_hasType
    {source : DependentCalculus.Context n}
    {domain : CoreTerm n} {body codomain : CoreTerm (n + 1)}
    {domainLevel codomainLevel : Nat}
    (translatedWellFormed : WellFormed (context source))
    (domainWellTyped :
      DependentCalculus.HasType source domain (.sort domainLevel))
    (codomainWellTyped :
      DependentCalculus.HasType (.extend source domain)
        codomain (.sort codomainLevel))
    (bodyWellTyped :
      DependentCalculus.HasType (.extend source domain) body codomain)
    (domainWitness :
      HasType (context source) (termTranslation domain)
        (relatedTermType domain (.sort domainLevel)))
    (codomainWitness :
      HasType (context (.extend source domain)) (termTranslation codomain)
        (relatedTermType codomain (.sort codomainLevel)))
    (bodyWitness :
      HasType (context (.extend source domain)) (termTranslation body)
        (relatedTermType body codomain)) :
    HasType (context source) (termTranslation (.lam domain body))
      (relatedTermType (.lam domain body) (.pi domain codomain)) := by
  have extension := context_extend_wellFormed translatedWellFormed
    domainWellTyped domainWitness
  have originalDomain :
      HasType (context source) (original domain) (.sort domainLevel) := by
    simpa only [original, RawParametricity.original,
      DependentCalculus.Term.rename, Term.ofCore] using
      HasType.original domainWellTyped translatedWellFormed
  have firstWellFormed : WellFormed (.extend (context source) (original domain)) :=
    .extend translatedWellFormed originalDomain
  have primedDomainBase :
      HasType (context source) (primed domain) (.sort domainLevel) := by
    simpa only [primed, RawParametricity.primed,
      DependentCalculus.Term.rename, Term.ofCore] using
      HasType.primed domainWellTyped translatedWellFormed
  have primedDomain :
      HasType (.extend (context source) (original domain))
        ((primed domain).weakenBy 1) (.sort domainLevel) := by
    simpa only [Term.weakenBy, Term.rename] using
      primedDomainBase.weaken firstWellFormed
  have relatedDomain := extension.2
  have lambdaWellTyped :
      DependentCalculus.HasType source (.lam domain body)
        (.pi domain codomain) :=
    .lam domainWellTyped bodyWellTyped
  have fiberBodyWellTyped := fiberApplication_hasType lambdaWellTyped
    codomainWellTyped.contextWellFormed
  have outputWellTyped := relatedTermType_hasType_of_typeWitness extension.1
    fiberBodyWellTyped codomainWellTyped codomainWitness
  rw [relatedTermType_fiberApplication] at outputWellTyped
  have bodyAtOutput :
      HasType (context (.extend source domain)) (termTranslation body)
        (applicationRelationBody (.lam domain body) codomain) :=
    .conversion bodyWitness outputWellTyped
      (lambdaApplicationRelationBody_convertible domain body codomain).symm
  have bodyAtOutput' :
      HasType
        (.extend
          (.extend (.extend (context source) (original domain))
            ((primed domain).weakenBy 1))
          (Term.relatedDomain (termTranslation domain)))
        (termTranslation body)
        (applicationRelationBody (.lam domain body) codomain) := by
    rw [context_extend] at bodyAtOutput
    exact bodyAtOutput
  have translatedLambdaNormal := HasType.lam originalDomain
    (HasType.lam primedDomain (HasType.lam relatedDomain bodyAtOutput'))
  have translatedLambdaNormal' :
      HasType (context source) (termTranslation (.lam domain body))
        (piRelationFiberNormal domain codomain (.lam domain body)) := by
    simpa only [termTranslation_lam, piRelationFiberNormal] using
      translatedLambdaNormal
  have productWellTyped :
      DependentCalculus.HasType source (.pi domain codomain)
        (.sort (max domainLevel codomainLevel)) :=
    .pi domainWellTyped codomainWellTyped
  have productWitness := termTranslation_pi_witness_hasType translatedWellFormed
    domainWellTyped codomainWellTyped extension.1 domainWitness codomainWitness
  have targetWellTyped := relatedTermType_hasType_of_typeWitness
    translatedWellFormed lambdaWellTyped productWellTyped productWitness
  have fiberConversion :=
    relatedTermType_pi_beta (.lam domain body) domain codomain
  rw [piRelationFiber_eq_normal] at fiberConversion
  exact .conversion translatedLambdaNormal' targetWellTyped fiberConversion.symm

/-- The translated universe satisfies the univalent witness conclusion. -/
theorem termTranslation_sort_witness_hasType
    {source : DependentCalculus.Context n}
    (translatedWellFormed : WellFormed (context source)) (level : Nat) :
    HasType (context source) (termTranslation (.sort level : CoreTerm n))
      (relatedTermType (.sort level) (.sort (level + 1))) := by
  change HasType (context source) (.universePackage level)
    (translatedUniversePackageType level)
  exact universePackage_hasType_translatedUniverse translatedWellFormed level

/-- A translated variable is typed by its relation-witness context entry. -/
theorem termTranslation_var_witness_hasType
    {source : DependentCalculus.Context n}
    (translatedWellFormed : WellFormed (context source)) (index : Fin n) :
    HasType (context source) (termTranslation (.var index))
      (relatedTermType (.var index) (source.lookup index)) := by
  have witnessVariable := HasType.var translatedWellFormed
    (RawParametricity.witnessRenaming n index)
  rw [Context.translated_lookup_witness] at witnessVariable
  simpa only [termTranslation_var] using witnessVariable

/-- Formation-explicit typing yields translated-context formation and witness typing. -/
theorem formationStructural
    {source : DependentCalculus.Context n}
    {term type : CoreTerm n}
    (termWellTyped : RawParametricity.FormationHasType source term type) :
    WellFormed (context source) ∧
      HasType (context source) (termTranslation term) (relatedTermType term type) := by
  refine RawParametricity.FormationHasType.rec
    (motive_1 := fun source _ => WellFormed (context source))
    (motive_2 := fun source term type _ =>
      WellFormed (context source) ∧
        HasType (context source) (termTranslation term) (relatedTermType term type))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · simpa only [context_empty, scopeSize, RawParametricity.scopeSize] using
      (WellFormed.empty : WellFormed Context.empty)
  · intro _ _ _ _ _ typeWellTyped sourceInduction typeInduction
    exact (context_extend_wellFormed sourceInduction
      typeWellTyped.erase typeInduction.2).1
  · intro _ _ _ level sourceInduction
    exact ⟨sourceInduction, termTranslation_sort_witness_hasType sourceInduction level⟩
  · intro _ _ _ index sourceInduction
    exact ⟨sourceInduction, termTranslation_var_witness_hasType sourceInduction index⟩
  · intro _ _ _ _ _ _ functionWellTyped argumentWellTyped
      functionInduction argumentInduction
    exact ⟨functionInduction.1,
      termTranslation_app_witness_hasType_of_witnesses functionInduction.1
        functionWellTyped.erase argumentWellTyped.erase
        functionInduction.2 argumentInduction.2⟩
  · intro _ source domain body codomain domainLevel codomainLevel
      domainWellTyped codomainWellTyped bodyWellTyped
      domainInduction codomainInduction bodyInduction
    exact ⟨domainInduction.1,
      termTranslation_lam_witness_hasType
        domainInduction.1 domainWellTyped.erase codomainWellTyped.erase
        bodyWellTyped.erase domainInduction.2 codomainInduction.2 bodyInduction.2⟩
  · intro _ _ _ _ _ _ domainWellTyped codomainWellTyped
      domainInduction codomainInduction
    exact ⟨domainInduction.1,
      termTranslation_pi_witness_hasType domainInduction.1
        domainWellTyped.erase codomainWellTyped.erase codomainInduction.1
        domainInduction.2 codomainInduction.2⟩
  · intro _ _ _ _ _ _ termWellTyped targetWellTyped equal
      termInduction targetInduction
    have targetRelationWellTyped := relatedTermType_hasType_of_typeWitness
      termInduction.1
      (.conversion termWellTyped.erase targetWellTyped.erase equal)
      targetWellTyped.erase targetInduction.2
    exact ⟨termInduction.1,
      .conversion termInduction.2 targetRelationWellTyped
        (relatedTermType_convertible _ equal)⟩
  · intro _ source term _ type' _ termWellTyped targetWellTyped
      subtype termInduction targetInduction
    have raisedTerm : DependentCalculus.HasType source term type' :=
      .cumulativity termWellTyped.erase targetWellTyped.erase subtype
    have targetRelationWellTyped := relatedTermType_hasType_of_typeWitness
      termInduction.1 raisedTerm targetWellTyped.erase targetInduction.2
    exact ⟨termInduction.1,
      .cumulativity termInduction.2 targetRelationWellTyped
        (relatedTermType_cumulative term subtype)⟩

/-- The witness judgment asserted by univalent abstraction. -/
def UnivalentAbstractionClaim : Prop :=
  ∀ {n : Nat} {source : DependentCalculus.Context n}
    {term type : CoreTerm n},
    DependentCalculus.HasType source term type →
      HasType (context source) (termTranslation term) (relatedTermType term type)

/-- A formation-explicit derivation yields its translated witness judgment. -/
theorem formationWitness
    {source : DependentCalculus.Context n}
    {term type : CoreTerm n}
    (termWellTyped : RawParametricity.FormationHasType source term type) :
    HasType (context source) (termTranslation term) (relatedTermType term type) :=
  (formationStructural termWellTyped).2

/-- A formation-explicit derivation forms its translated context. -/
theorem formationTranslatedContextWellFormed
    {source : DependentCalculus.Context n}
    {term type : CoreTerm n}
    (termWellTyped : RawParametricity.FormationHasType source term type) :
    WellFormed (context source) :=
  (formationStructural termWellTyped).1

/-- Ordinary dependent typing yields translated-context formation and witness typing. -/
theorem structuralUnivalentAbstraction : StructuralAbstractionClaim :=
  fun termWellTyped =>
    formationStructural (RawParametricity.FormationHasType.ofHasType termWellTyped)

/-- Formation-explicit typing satisfies all three displayed typing conclusions. -/
theorem formationExplicitUnivalentAbstraction
    {source : DependentCalculus.Context n}
    {term type : CoreTerm n}
    (termWellTyped : RawParametricity.FormationHasType source term type) :
    AbstractionConclusion source term type := by
  have translatedWellFormed :=
    formationTranslatedContextWellFormed termWellTyped
  exact ⟨HasType.original termWellTyped.erase translatedWellFormed,
    HasType.primed termWellTyped.erase translatedWellFormed,
    formationWitness termWellTyped⟩

/-- Ordinary dependent typing satisfies univalent witness abstraction. -/
theorem univalentAbstraction : UnivalentAbstractionClaim :=
  fun termWellTyped => (structuralUnivalentAbstraction termWellTyped).2

/-- Ordinary dependent typing forms the translation and satisfies displayed abstraction. -/
theorem fullUnivalentAbstraction : AbstractionClaim := fun termWellTyped => by
  have formationTyping := RawParametricity.FormationHasType.ofHasType termWellTyped
  exact ⟨formationTranslatedContextWellFormed formationTyping,
    formationExplicitUnivalentAbstraction formationTyping⟩

/-- Ordinary dependent typing satisfies all three displayed abstraction conclusions. -/
theorem displayedUnivalentAbstraction : DisplayedAbstractionClaim :=
  fun termWellTyped => (fullUnivalentAbstraction termWellTyped).2

example : UnivalentAbstractionClaim :=
  univalentAbstraction

end DeepWiki.Refine.DependentCalculus.UnivalentParametricity
