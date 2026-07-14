import DeepWiki.Refine.DependentCalculusCumulativeInversion

/-! # Subject reduction for the dependent calculus

Compatible beta reduction preserves typing once cumulative products expose their contra- and
covariant components.  Canonically introduced beta redexes preserve typing unconditionally.
-/

namespace DeepWiki.Refine.DependentCalculus

/-- Product-component inversion proves subject reduction for a typed root beta contraction. -/
theorem rootBetaSubjectReduction_of_cumulativeProductComponentInversion
    (inversion : CumulativeProductComponentInversion)
    {context : Context n} {domain argument type : Term n} {body : Term (n + 1)}
    (redexWellTyped : HasType context (.app (.lam domain body) argument) type) :
    HasType context (body.instantiate argument) type := by
  obtain ⟨targetDomain, targetCodomain, lambdaWellTyped, argumentWellTyped,
      resultLower⟩ := redexWellTyped.app_principal
  obtain ⟨bodyType, bodyWellTyped, productLower⟩ := lambdaWellTyped.lam_principal
  obtain ⟨_domainType, domainLevel, domainWellTyped, _bodyWellTyped'⟩ :=
    lambdaWellTyped.lamComponents
  obtain ⟨domainLower, codomainLower⟩ := inversion productLower
  have argumentAtDisplayedDomain : HasType context argument domain :=
    .cumulativity argumentWellTyped domainWellTyped domainLower
  have reductAtBodyType :
      HasType context (body.instantiate argument) (bodyType.instantiate argument) :=
    bodyWellTyped.instantiate redexWellTyped.contextWellFormed argumentAtDisplayedDomain
  have applicationAtTargetCodomain :
      HasType context (.app (.lam domain body) argument)
        (targetCodomain.instantiate argument) :=
    .app lambdaWellTyped argumentWellTyped
  obtain ⟨targetCodomainLevel, targetCodomainWellTyped⟩ :=
    applicationAtTargetCodomain.typeWellTyped
  have reductAtTargetCodomain :
      HasType context (body.instantiate argument)
        (targetCodomain.instantiate argument) :=
    .cumulativity reductAtBodyType targetCodomainWellTyped
      (codomainLower.substitute (Substitution.single argument))
  obtain ⟨typeLevel, typeWellTyped⟩ := redexWellTyped.typeWellTyped
  exact .cumulativity reductAtTargetCodomain typeWellTyped resultLower

namespace Convertible

/-- Conversion of an argument induces conversion after dependent instantiation. -/
theorem instantiate_argument {argument argument' : Term n}
    (conversion : Convertible argument argument') (body : Term (n + 1)) :
    Convertible (body.instantiate argument) (body.instantiate argument') := by
  induction conversion generalizing body with
  | refl => exact .refl _
  | beta step => exact ((Parallel.refl body).instantiate step.parallel).convertible
  | symm _ inductionHypothesis => exact (inductionHypothesis body).symm
  | trans _ _ firstInduction secondInduction =>
      exact (firstInduction body).trans (secondInduction body)

end Convertible

namespace HasType

/-- A canonically introduced beta redex and its contractum have the same dependent type. -/
theorem canonicalBetaRedex_subjectReduction
    {context : Context n} {domain argument : Term n} {body codomain : Term (n + 1)}
    {domainLevel : Nat}
    (domainWellTyped : HasType context domain (.sort domainLevel))
    (bodyWellTyped : HasType (.extend context domain) body codomain)
    (argumentWellTyped : HasType context argument domain) :
    HasType context (.app (.lam domain body) argument)
        (codomain.instantiate argument) ∧
      HasType context (body.instantiate argument)
        (codomain.instantiate argument) := by
  constructor
  · exact .app (.lam domainWellTyped bodyWellTyped) argumentWellTyped
  · exact bodyWellTyped.instantiate domainWellTyped.contextWellFormed argumentWellTyped

/-- Root-beta preservation suffices for every compatible one-step beta reduction. -/
private theorem subjectReduction_of_rootBeta
    (rootBeta : ∀ {n : Nat} {context : Context n} {domain argument type : Term n}
      {body : Term (n + 1)},
      HasType context (.app (.lam domain body) argument) type →
        HasType context (body.instantiate argument) type)
    {context : Context n} {term term' type : Term n}
    (termWellTyped : HasType context term type) (step : BetaStep term term') :
    HasType context term' type := by
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context term type _ =>
      ∀ {term'}, BetaStep term term' → HasType context term' type)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped step
  · trivial
  · intros
    trivial
  · intro _ _ contextWellFormed level _ term' impossible
    cases impossible
  · intro _ _ contextWellFormed index _ term' impossible
    cases impossible
  · intro _ context function argument domain codomain functionWellTyped argumentWellTyped
      functionInduction argumentInduction term' applicationStep
    cases applicationStep with
    | beta redexDomain redexBody redexArgument =>
        exact rootBeta (.app functionWellTyped argumentWellTyped)
    | appFunction functionStep =>
        exact .app (functionInduction functionStep) argumentWellTyped
    | appArgument argumentStep =>
        have reducedApplication :=
          HasType.app functionWellTyped (argumentInduction argumentStep)
        obtain ⟨targetLevel, targetTypeWellTyped⟩ :=
          (HasType.app functionWellTyped argumentWellTyped).typeWellTyped
        exact .conversion reducedApplication targetTypeWellTyped
          ((Convertible.beta argumentStep).symm.instantiate_argument codomain)
  · intro _ context domain body codomain domainLevel domainWellTyped bodyWellTyped
      domainInduction bodyInduction term' lambdaStep
    cases lambdaStep with
    | lamDomain domainStep =>
        have reducedDomainWellTyped := domainInduction domainStep
        have narrowedBody := bodyWellTyped.narrowExtension domainWellTyped
          reducedDomainWellTyped (.conversion (Convertible.beta domainStep).symm)
        have reducedLambda := HasType.lam reducedDomainWellTyped narrowedBody
        obtain ⟨targetLevel, targetTypeWellTyped⟩ :=
          (HasType.lam domainWellTyped bodyWellTyped).typeWellTyped
        exact .conversion reducedLambda targetTypeWellTyped
          ((Convertible.beta domainStep).symm.pi_domain)
    | lamBody bodyStep =>
        exact .lam domainWellTyped (bodyInduction bodyStep)
  · intro _ context domain codomain domainLevel codomainLevel domainWellTyped
      codomainWellTyped domainInduction codomainInduction term' productStep
    cases productStep with
    | piDomain domainStep =>
        have reducedDomainWellTyped := domainInduction domainStep
        have narrowedCodomain := codomainWellTyped.narrowExtension domainWellTyped
          reducedDomainWellTyped (.conversion (Convertible.beta domainStep).symm)
        exact .pi reducedDomainWellTyped narrowedCodomain
    | piCodomain codomainStep =>
        exact .pi domainWellTyped (codomainInduction codomainStep)
  · intro _ context term sourceType targetType level termWellTyped targetWellTyped equal
      termInduction _targetInduction term' termStep
    exact .conversion (termInduction termStep) targetWellTyped equal
  · intro _ context term sourceType targetType level termWellTyped targetWellTyped subtype
      termInduction _targetInduction term' termStep
    exact .cumulativity (termInduction termStep) targetWellTyped subtype

/-- Product-component inversion proves full compatible one-step subject reduction. -/
theorem subjectReduction_of_cumulativeProductComponentInversion
    (inversion : CumulativeProductComponentInversion)
    {context : Context n} {term term' type : Term n}
    (termWellTyped : HasType context term type) (step : BetaStep term term') :
    HasType context term' type :=
  termWellTyped.subjectReduction_of_rootBeta
    (rootBetaSubjectReduction_of_cumulativeProductComponentInversion inversion) step

end HasType

example {context : Context n} {domain argument : Term n}
    {body codomain : Term (n + 1)} {domainLevel : Nat}
    (domainWellTyped : HasType context domain (.sort domainLevel))
    (bodyWellTyped : HasType (.extend context domain) body codomain)
    (argumentWellTyped : HasType context argument domain) :
    HasType context (body.instantiate argument) (codomain.instantiate argument) :=
  (HasType.canonicalBetaRedex_subjectReduction domainWellTyped bodyWellTyped
    argumentWellTyped).2

end DeepWiki.Refine.DependentCalculus
