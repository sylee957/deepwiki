import DeepWiki.Refine.CCOmega.Confluence

/-! # Principal typing for the dependent calculus

Typing derivations factor through constructor-local principal types. The exact cumulative
product/sort separation boundary is recorded for the erasure proof downstream.
-/

namespace DeepWiki.Refine.DependentCalculus

namespace Parallel

/-- A parallel reduction is included in beta conversion. -/
theorem convertible {left right : Term n} (step : Parallel left right) :
    Convertible left right := by
  induction step with
  | var index => exact .refl (.var index)
  | sort level => exact .refl (.sort level)
  | app _ _ functionInduction argumentInduction =>
      exact functionInduction.app_function.trans argumentInduction.app_argument
  | lam _ _ domainInduction bodyInduction =>
      exact domainInduction.lam_domain.trans bodyInduction.lam_body
  | pi _ _ domainInduction codomainInduction =>
      exact domainInduction.pi_domain.trans codomainInduction.pi_codomain
  | beta _ _ _ domainInduction bodyInduction argumentInduction =>
      have functionConversion :
          Convertible (.lam _ _) (.lam _ _) :=
        domainInduction.lam_domain.trans bodyInduction.lam_body
      have redexConversion :
          Convertible (.app (.lam _ _) _) (.app (.lam _ _) _) :=
        functionConversion.app_function.trans argumentInduction.app_argument
      exact redexConversion.trans (.beta (.beta _ _ _))

/-- A reflexive-transitive parallel reduction is included in beta conversion. -/
theorem star_convertible {left right : Term n}
    (steps : Relation.ReflTransGen (@Parallel n) left right) :
    Convertible left right := by
  induction steps with
  | refl => exact .refl _
  | tail _ lastStep inductionHypothesis =>
      exact inductionHypothesis.trans lastStep.convertible

end Parallel

/-- Parallel reduction from a product retains componentwise parallel reductions. -/
theorem parallelStar_pi_components {domain : Term n} {codomain : Term (n + 1)}
    {target : Term n}
    (steps : Relation.ReflTransGen (@Parallel n) (.pi domain codomain) target) :
    ∃ domain' codomain',
      target = .pi domain' codomain' ∧
        Relation.ReflTransGen (@Parallel n) domain domain' ∧
          Relation.ReflTransGen (@Parallel (n + 1)) codomain codomain' := by
  induction steps with
  | refl => exact ⟨domain, codomain, rfl, .refl, .refl⟩
  | tail _ lastStep inductionHypothesis =>
      obtain ⟨domain', codomain', rfl, domainSteps, codomainSteps⟩ :=
        inductionHypothesis
      obtain ⟨domain'', codomain'', rfl, domainStep, codomainStep⟩ :=
        lastStep.pi_target
      exact ⟨domain'', codomain'', rfl, domainSteps.tail domainStep,
        codomainSteps.tail codomainStep⟩

namespace Convertible

/-- Conversion between products exposes conversion between their corresponding components. -/
theorem pi_components {domain domain' : Term n}
    {codomain codomain' : Term (n + 1)}
    (conversion : Convertible (.pi domain codomain) (.pi domain' codomain')) :
    Convertible domain domain' ∧ Convertible codomain codomain' := by
  obtain ⟨common, leftSteps, rightSteps⟩ := conversion.parallelJoin
  obtain ⟨leftDomain, leftCodomain, commonShape, leftDomainSteps, leftCodomainSteps⟩ :=
    parallelStar_pi_components leftSteps
  obtain ⟨rightDomain, rightCodomain, commonShape', rightDomainSteps,
      rightCodomainSteps⟩ := parallelStar_pi_components rightSteps
  rw [commonShape] at commonShape'
  injection commonShape' with _ domainEqual codomainEqual
  cases domainEqual
  cases codomainEqual
  exact ⟨(Parallel.star_convertible leftDomainSteps).trans
      (Parallel.star_convertible rightDomainSteps).symm,
    (Parallel.star_convertible leftCodomainSteps).trans
      (Parallel.star_convertible rightCodomainSteps).symm⟩

end Convertible

/-- A constructor-local principal type lies cumulatively below an assigned type. -/
def HasPrincipalType {n : Nat} (context : Context n) (term type : Term n) : Prop :=
  match term with
  | .sort level => Cumulative (.sort (level + 1)) type
  | .var index => Cumulative (context.lookup index) type
  | .app function argument =>
      ∃ domain codomain,
        HasType context function (.pi domain codomain) ∧
          HasType context argument domain ∧
            Cumulative (codomain.instantiate argument) type
  | .lam domain body =>
      ∃ codomain,
        HasType (.extend context domain) body codomain ∧
          Cumulative (.pi domain codomain) type
  | .pi _domain _codomain => ∃ level, Cumulative (.sort level) type

namespace HasPrincipalType

/-- Raising an assigned type preserves its constructor-local principal type. -/
theorem cumulative {context : Context n} {term type type' : Term n}
    (principal : HasPrincipalType context term type)
    (subtype : Cumulative type type') :
    HasPrincipalType context term type' := by
  cases term with
  | sort level =>
      exact principal.trans subtype
  | var index =>
      exact principal.trans subtype
  | app function argument =>
      obtain ⟨domain, codomain, functionWellTyped, argumentWellTyped, lower⟩ := principal
      exact ⟨domain, codomain, functionWellTyped, argumentWellTyped, lower.trans subtype⟩
  | lam domain body =>
      obtain ⟨codomain, bodyWellTyped, lower⟩ := principal
      exact ⟨codomain, bodyWellTyped, lower.trans subtype⟩
  | pi domain codomain =>
      obtain ⟨level, lower⟩ := principal
      exact ⟨level, lower.trans subtype⟩

end HasPrincipalType

namespace HasType

/-- Every typing derivation factors through a constructor-local principal type. -/
theorem principal {context : Context n} {term type : Term n}
    (termWellTyped : HasType context term type) :
    HasPrincipalType context term type := by
  refine HasType.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun context term type _ => HasPrincipalType context term type)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · trivial
  · intros
    trivial
  · intro _ _ _ level _
    exact Cumulative.refl (.sort (level + 1))
  · intro _ context _ index _
    exact Cumulative.refl (context.lookup index)
  · intro _ _ function argument domain codomain functionWellTyped argumentWellTyped _ _
    exact ⟨domain, codomain, functionWellTyped, argumentWellTyped, .refl _⟩
  · intro _ _ domain body codomain _ domainWellTyped bodyWellTyped _ _
    exact ⟨codomain, bodyWellTyped, .refl _⟩
  · intro _ _ _ _ domainLevel codomainLevel _ _ _ _
    exact ⟨max domainLevel codomainLevel, .refl _⟩
  · intro _ _ _ _ _ _ _ _ equal inductionHypothesis _
    exact inductionHypothesis.cumulative (.conversion equal)
  · intro _ _ _ _ _ _ _ _ subtype inductionHypothesis _
    exact inductionHypothesis.cumulative subtype

/-- Every assigned type of a universe term is cumulatively above its successor universe. -/
theorem sort_principal {context : Context n} {level : Nat} {type : Term n}
    (termWellTyped : HasType context (.sort level) type) :
    Cumulative (.sort (level + 1)) type :=
  termWellTyped.principal

/-- Every assigned type of a variable is cumulatively above its context lookup. -/
theorem var_principal {context : Context n} {index : Fin n} {type : Term n}
    (termWellTyped : HasType context (.var index) type) :
    Cumulative (context.lookup index) type :=
  termWellTyped.principal

/-- Every assigned type of an application lies above an instantiated result from an application rule. -/
theorem app_principal {context : Context n} {function argument type : Term n}
    (termWellTyped : HasType context (.app function argument) type) :
    ∃ domain codomain,
      HasType context function (.pi domain codomain) ∧
        HasType context argument domain ∧
          Cumulative (codomain.instantiate argument) type :=
  termWellTyped.principal

/-- Every assigned type of a lambda lies above a product introduced by a lambda rule. -/
theorem lam_principal {context : Context n} {domain : Term n}
    {body : Term (n + 1)} {type : Term n}
    (termWellTyped : HasType context (.lam domain body) type) :
    ∃ codomain,
      HasType (.extend context domain) body codomain ∧
        Cumulative (.pi domain codomain) type :=
  termWellTyped.principal

/-- Every assigned type of a product lies above a universe introduced by a product rule. -/
theorem pi_principal {context : Context n} {domain : Term n}
    {codomain : Term (n + 1)} {type : Term n}
    (termWellTyped : HasType context (.pi domain codomain) type) :
    ∃ level, Cumulative (.sort level) type :=
  termWellTyped.principal

end HasType

end DeepWiki.Refine.DependentCalculus
