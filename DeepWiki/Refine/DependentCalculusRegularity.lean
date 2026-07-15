import DeepWiki.Refine.AnnotatedCalculusConservativity

/-! # Regularity of dependent context extension

Narrowing the newest context entry is realized by a typed identity substitution.  The newest
variable is transported by cumulativity, while every older lookup is definitionally unchanged.
-/

namespace DeepWiki.Refine.DependentCalculus

namespace TypedSubstitution

/-- Identity substitution narrows the newest context entry along cumulative conversion. -/
theorem narrowExtension {context : Context n} {domain domain' : Term n}
    {domainLevel domainLevel' : Nat}
    (domainWellTyped : HasType context domain (.sort domainLevel))
    (domain'WellTyped : HasType context domain' (.sort domainLevel'))
    (domainCumulative : Cumulative domain' domain) :
    TypedSubstitution (.extend context domain) (.extend context domain')
      Substitution.identity where
  targetWellFormed := .extend domain'WellTyped.contextWellFormed domain'WellTyped
  variableWellTyped index := by
    let targetWellFormed : WellFormed (.extend context domain') :=
      .extend domain'WellTyped.contextWellFormed domain'WellTyped
    refine Fin.cases ?_ ?_ index
    · have newestWellTyped :
        HasType (.extend context domain') (.var 0)
          (domain'.rename Renaming.shift) :=
        .var targetWellFormed 0
      have targetTypeWellTyped :
          HasType (.extend context domain') (domain.rename Renaming.shift)
            (.sort domainLevel) :=
        domainWellTyped.weaken targetWellFormed
      have narrowed :
          HasType (.extend context domain') (.var 0)
            (domain.rename Renaming.shift) :=
        .cumulativity newestWellTyped targetTypeWellTyped
          (domainCumulative.rename Renaming.shift)
      change HasType (.extend context domain') (.var 0)
        ((domain.rename Renaming.shift).substitute Substitution.identity)
      simpa only [Term.substitute_identity] using narrowed
    · intro older
      have olderWellTyped := HasType.var targetWellFormed older.succ
      change HasType (.extend context domain') (.var older.succ)
        (((context.lookup older).rename Renaming.shift).substitute
          Substitution.identity)
      simpa only [Context.lookup_succ, Term.substitute_identity] using olderWellTyped

end TypedSubstitution

namespace HasType

/-- Narrowing the newest context entry preserves dependent typing without changing syntax. -/
theorem narrowExtension {context : Context n} {domain domain' : Term n}
    {term type : Term (n + 1)} {domainLevel domainLevel' : Nat}
    (termWellTyped : HasType (.extend context domain) term type)
    (domainWellTyped : HasType context domain (.sort domainLevel))
    (domain'WellTyped : HasType context domain' (.sort domainLevel'))
    (domainCumulative : Cumulative domain' domain) :
    HasType (.extend context domain') term type := by
  have narrowed := termWellTyped.substitute
    (TypedSubstitution.narrowExtension domainWellTyped domain'WellTyped domainCumulative)
  simpa only [Term.substitute_identity] using narrowed

end HasType

end DeepWiki.Refine.DependentCalculus

namespace DeepWiki.Refine.AnnotatedCalculusConservativity

/-- A term assigned both a universe and a syntactic kind can only have a universe kind. -/
def AssignedKindSortDiscrimination : Prop :=
  ∀ {n : Nat} {context : DependentCalculus.Context n}
    {term kind : DependentCalculus.Term n},
    DependentCalculus.IsKind kind →
      DependentCalculus.HasType context term kind →
      IsUniverseTyped context term →
        ∃ level, kind = .sort level

/-- Kind-sort discrimination implies typed conversion universe regularity. -/
theorem typedConversionUniverseRegularity_of_assignedKindSortDiscrimination
    (discrimination : AssignedKindSortDiscrimination) :
    TypedConversionUniverseRegularity := by
  intro n context left right kind kindShape leftWellTyped rightWellTyped
    _equal leftUniverseTyped
  obtain ⟨level, rfl⟩ :=
    discrimination kindShape leftWellTyped leftUniverseTyped
  exact ⟨level, rightWellTyped⟩

/-- The ordinary dependent calculus satisfies newest-entry context narrowing. -/
theorem dependentContextNarrowing : DependentContextNarrowing := by
  intro n context domain domain' term type domainWellTyped domain'WellTyped
    domainCumulative termWellTyped
  obtain ⟨domainLevel, domainWellTyped⟩ := domainWellTyped
  obtain ⟨domainLevel', domain'WellTyped⟩ := domain'WellTyped
  exact termWellTyped.narrowExtension domainWellTyped domain'WellTyped domainCumulative

/-- Product typehood follows from reverse domain transport and forward narrowed-codomain transport. -/
theorem piUniverseTyped_of_transport
    {context : DependentCalculus.Context n}
    {domain domain' : DependentCalculus.Term n}
    {codomain codomain' : DependentCalculus.Term (n + 1)}
    (domainCumulative : DependentCalculus.Cumulative domain' domain)
    (domainTypehood : IsUniverseTyped context domain →
      IsUniverseTyped context domain')
    (codomainTypehood : IsUniverseTyped (.extend context domain') codomain →
      IsUniverseTyped (.extend context domain') codomain')
    (productTypehood : IsUniverseTyped context (.pi domain codomain)) :
    IsUniverseTyped context (.pi domain' codomain') := by
  obtain ⟨_, productWellTyped⟩ := productTypehood
  obtain ⟨domainLevel, codomainLevel, domainWellTyped, codomainWellTyped⟩ :=
    productWellTyped.piComponents
  obtain ⟨domainLevel', domain'WellTyped⟩ :=
    domainTypehood ⟨domainLevel, domainWellTyped⟩
  have narrowedCodomain := codomainWellTyped.narrowExtension
    domainWellTyped domain'WellTyped domainCumulative
  obtain ⟨codomainLevel', codomain'WellTyped⟩ :=
    codomainTypehood ⟨codomainLevel, narrowedCodomain⟩
  exact ⟨max domainLevel' codomainLevel',
    .pi domain'WellTyped codomain'WellTyped⟩

/-- Product typehood is covariant when both component subtype steps transport typehood both ways. -/
theorem piUniverseTyped_of_bidirectional_transport
    {context : DependentCalculus.Context n}
    {domain domain' : DependentCalculus.Term n}
    {codomain codomain' : DependentCalculus.Term (n + 1)}
    (domainCumulative : DependentCalculus.Cumulative domain' domain)
    (domainTypehood : IsUniverseTyped context domain' ↔
      IsUniverseTyped context domain)
    (codomainTypehood : IsUniverseTyped (.extend context domain') codomain ↔
      IsUniverseTyped (.extend context domain') codomain')
    (productTypehood : IsUniverseTyped context (.pi domain codomain)) :
    IsUniverseTyped context (.pi domain' codomain') :=
  piUniverseTyped_of_transport domainCumulative domainTypehood.mpr
    codomainTypehood.mp productTypehood

example : DependentContextNarrowing :=
  dependentContextNarrowing

example (discrimination : AssignedKindSortDiscrimination) :
    TypedConversionUniverseRegularity :=
  typedConversionUniverseRegularity_of_assignedKindSortDiscrimination discrimination

example {context : DependentCalculus.Context n}
    {domain domain' : DependentCalculus.Term n}
    {codomain codomain' : DependentCalculus.Term (n + 1)}
    (domainCumulative : DependentCalculus.Cumulative domain' domain)
    (domainTypehood : IsUniverseTyped context domain' ↔
      IsUniverseTyped context domain)
    (codomainTypehood : IsUniverseTyped (.extend context domain') codomain ↔
      IsUniverseTyped (.extend context domain') codomain')
    (productTypehood : IsUniverseTyped context (.pi domain codomain)) :
    IsUniverseTyped context (.pi domain' codomain') :=
  piUniverseTyped_of_bidirectional_transport domainCumulative domainTypehood
    codomainTypehood productTypehood

end DeepWiki.Refine.AnnotatedCalculusConservativity
