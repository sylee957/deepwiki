import DeepWiki.Refine.RawParametricityTyping

/-! # Conversion for raw parametricity

Raw translation preserves compatible beta reduction and definitional conversion, and the typing
conversion rule preserves relational witness typing. -/

namespace DeepWiki.Refine.DependentCalculus.RawParametricity

/-- Translating a beta redex contracts the three original, primed, and witness arguments. -/
theorem translate_beta_redex (domain : Term n) (body : Term (n + 1))
    (argument : Term n) :
    Convertible (translate (.app (.lam domain body) argument))
      (translate (body.instantiate argument)) := by
  rw [translate_app, translate_lam]
  refine .trans (.app_function (.app_function (.beta (.beta _ _ _)))) ?_
  refine .trans (.app_function (.beta (.beta _ _ _))) ?_
  refine .trans (.beta (.beta _ _ _)) ?_
  rw [translate_instantiate_normalized]
  rw [← substitute_relationalSingle]
  exact .refl _

namespace Convertible

/-- Conversion is congruent in both the function and argument of an application. -/
theorem app_both {function function' argument argument' : Term n}
    (functionConversion : Convertible function function')
    (argumentConversion : Convertible argument argument') :
    Convertible (.app function argument) (.app function' argument') :=
  functionConversion.app_function.trans argumentConversion.app_argument

/-- Conversion is congruent in both the domain and body of a lambda. -/
theorem lam_both {domain domain' : Term n} {body body' : Term (n + 1)}
    (domainConversion : Convertible domain domain')
    (bodyConversion : Convertible body body') :
    Convertible (.lam domain body) (.lam domain' body') :=
  domainConversion.lam_domain.trans bodyConversion.lam_body

/-- Conversion is congruent in both the domain and codomain of a dependent product. -/
theorem pi_both {domain domain' : Term n} {codomain codomain' : Term (n + 1)}
    (domainConversion : Convertible domain domain')
    (codomainConversion : Convertible codomain codomain') :
    Convertible (.pi domain codomain) (.pi domain' codomain') :=
  domainConversion.pi_domain.trans codomainConversion.pi_codomain

/-- Weakening by any number of binders preserves definitional conversion. -/
theorem weakenBy {left right : Term n} (conversion : Convertible left right) :
    ∀ amount, Convertible (RawParametricity.weakenBy left amount)
      (RawParametricity.weakenBy right amount)
  | 0 => conversion
  | amount + 1 => (weakenBy conversion amount).rename Renaming.shift

end Convertible

/-- Application translation is congruent in all four translated components. -/
theorem translate_app_congr {function function' argument argument' : Term n}
    (functionConversion : Convertible (translate function) (translate function'))
    (originalArgumentConversion : Convertible (original argument) (original argument'))
    (primedArgumentConversion : Convertible (primed argument) (primed argument'))
    (argumentConversion : Convertible (translate argument) (translate argument')) :
    Convertible (translate (.app function argument))
      (translate (.app function' argument')) := by
  rw [translate_app, translate_app]
  exact Convertible.app_both
    (Convertible.app_both
      (Convertible.app_both functionConversion originalArgumentConversion)
      primedArgumentConversion)
    argumentConversion

/-- Lambda translation is congruent in its three domains and translated body. -/
theorem translate_lam_congr {domain domain' : Term n}
    {body body' : Term (n + 1)}
    (originalDomainConversion : Convertible (original domain) (original domain'))
    (primedDomainConversion : Convertible (primed domain) (primed domain'))
    (domainConversion : Convertible (translate domain) (translate domain'))
    (bodyConversion : Convertible (translate body) (translate body')) :
    Convertible (translate (.lam domain body)) (translate (.lam domain' body')) := by
  rw [translate_lam, translate_lam]
  exact Convertible.lam_both originalDomainConversion
    (Convertible.lam_both (Convertible.weakenBy primedDomainConversion 1)
      (Convertible.lam_both
        (Convertible.app_both
          (Convertible.app_both (Convertible.weakenBy domainConversion 2) (.refl _)) (.refl _))
        bodyConversion))

/-- Product translation is congruent in every copied domain and codomain component. -/
theorem translate_pi_congr {domain domain' : Term n}
    {codomain codomain' : Term (n + 1)}
    (originalProductConversion :
      Convertible (original (.pi domain codomain)) (original (.pi domain' codomain')))
    (primedProductConversion :
      Convertible (primed (.pi domain codomain)) (primed (.pi domain' codomain')))
    (originalDomainConversion : Convertible (original domain) (original domain'))
    (primedDomainConversion : Convertible (primed domain) (primed domain'))
    (domainConversion : Convertible (translate domain) (translate domain'))
    (codomainConversion : Convertible (translate codomain) (translate codomain')) :
    Convertible (translate (.pi domain codomain)) (translate (.pi domain' codomain')) := by
  rw [translate_pi, translate_pi]
  exact Convertible.lam_both originalProductConversion
    (Convertible.lam_both (Convertible.weakenBy primedProductConversion 1)
      (Convertible.pi_both (Convertible.weakenBy originalDomainConversion 2)
        (Convertible.pi_both (Convertible.weakenBy primedDomainConversion 3)
          (Convertible.pi_both
            (Convertible.app_both
              (Convertible.app_both (Convertible.weakenBy domainConversion 4) (.refl _)) (.refl _))
            (Convertible.app_both
              (Convertible.app_both
                (codomainConversion.rename insertTwoAfterThree) (.refl _))
              (.refl _))))))

/-- Original-copy renaming sends a beta step to definitional conversion. -/
theorem original_betaStep {left right : Term n} (step : BetaStep left right) :
    Convertible (original left) (original right) :=
  .beta (step.rename (originalRenaming n))

/-- Primed-copy renaming sends a beta step to definitional conversion. -/
theorem primed_betaStep {left right : Term n} (step : BetaStep left right) :
    Convertible (primed left) (primed right) :=
  .beta (step.rename (primedRenaming n))

/-- Raw parametricity translation sends compatible beta reduction to conversion. -/
theorem translate_betaStep {left right : Term n} (step : BetaStep left right) :
    Convertible (translate left) (translate right) := by
  induction step with
  | beta domain body argument =>
      exact translate_beta_redex domain body argument
  | appFunction step inductionHypothesis =>
      exact translate_app_congr inductionHypothesis (.refl _) (.refl _) (.refl _)
  | appArgument step inductionHypothesis =>
      exact translate_app_congr (.refl _) (original_betaStep step)
        (primed_betaStep step) inductionHypothesis
  | @lamDomain n domain domain' body step inductionHypothesis =>
      exact translate_lam_congr (original_betaStep step) (primed_betaStep step)
        inductionHypothesis (.refl _)
  | @lamBody n domain body body' step inductionHypothesis =>
      exact translate_lam_congr (.refl _) (.refl _) (.refl _) inductionHypothesis
  | @piDomain n domain domain' codomain step inductionHypothesis =>
      exact translate_pi_congr (original_betaStep (.piDomain step))
        (primed_betaStep (.piDomain step)) (original_betaStep step)
        (primed_betaStep step) inductionHypothesis (.refl _)
  | @piCodomain n domain codomain codomain' step inductionHypothesis =>
      exact translate_pi_congr (original_betaStep (.piCodomain step))
        (primed_betaStep (.piCodomain step)) (.refl _) (.refl _) (.refl _)
        inductionHypothesis

/-- Original copies preserve definitional conversion. -/
theorem original_convertible {left right : Term n} (conversion : Convertible left right) :
    Convertible (original left) (original right) :=
  conversion.rename (originalRenaming n)

/-- Primed copies preserve definitional conversion. -/
theorem primed_convertible {left right : Term n} (conversion : Convertible left right) :
    Convertible (primed left) (primed right) :=
  conversion.rename (primedRenaming n)

/-- Raw parametricity translation preserves definitional conversion. -/
theorem translate_convertible {left right : Term n} (conversion : Convertible left right) :
    Convertible (translate left) (translate right) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact translate_betaStep step
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Changing a source type by conversion changes its related-term type by conversion. -/
theorem relatedTermType_convertible {term type type' : Term n}
    (conversion : Convertible type type') :
    Convertible (relatedTermType term type) (relatedTermType term type') := by
  unfold relatedTermType
  exact Convertible.app_both
    (Convertible.app_both (translate_convertible conversion) (.refl _)) (.refl _)

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

/-- The typing-conversion rule preserves the raw relational witness conclusion. -/
theorem translate_conversion_witness_hasType {source : Context n}
    {term type type' : Term n} {level : Nat}
    (translatedWellFormed : WellFormed (context source))
    (termWellTyped : HasType source term type)
    (targetWellTyped : HasType source type' (.sort level))
    (conversion : Convertible type type')
    (termWitness : HasType (context source) (translate term)
      (relatedTermType term type))
    (targetWitness : HasType (context source) (translate type')
      (relatedTermType type' (.sort level))) :
    HasType (context source) (translate term) (relatedTermType term type') := by
  have convertedTerm : HasType source term type' :=
    .conversion termWellTyped targetWellTyped conversion
  exact .conversion termWitness
    (relatedTermType_hasType_of_typeWitness translatedWellFormed convertedTerm
      targetWellTyped targetWitness)
    (relatedTermType_convertible conversion)

end DeepWiki.Refine.DependentCalculus.RawParametricity
