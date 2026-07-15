import DeepWiki.Refine.CCOmega.CumulativeInversion
import DeepWiki.Refine.ParametricitySequents

/-! # Counterexample to unrestricted raw parametricity abstraction

The unconstrained primed domain in the raw lambda sequent invalidates its unrestricted
abstraction claim, even for a closed source lambda and an empty context.
-/

namespace DeepWiki.Refine.DependentCalculus.ParametricitySequents

open RawParametricity

/-- The unrestricted raw abstraction claim fails because lambda translation need not preserve domains. -/
theorem not_rawAbstractionClaim : ¬ RawAbstractionClaim := by
  intro abstraction
  let typingContext : Context 0 := .empty
  let context : ParametricityContext 0 := []
  let domain : Term 0 := .sort 0
  let body : Term 1 := .sort 0
  let sourceType : Term 0 := .pi (.sort 0) (.sort 1)
  let primedDomain : Term 0 := .pi (.sort 0) (.var 0)
  let term : Term 0 := .lam domain body
  let term' : Term 0 := .lam primedDomain body
  let termRelation : Term 0 :=
    lambdaWitness domain primedDomain (.sort 0) (sortRelation 0 3)
  let typeRelation : Term 0 :=
    piWitness (.sort 0) (.sort 1) (.sort 0) (.sort 1)
      (sortRelation 0 0) (sortRelation 1 3)
  have admissible : Admissible typingContext context := by
    refine ⟨?_, .empty, ?_⟩
    · change ([] : List (Fin 0)).Nodup
      exact .nil
    · intro triple member
      simp [context] at member
  have sourceWellTyped : HasType typingContext term sourceType := by
    have domainWellTyped : HasType typingContext (.sort 0) (.sort 1) :=
      .sort .empty 0
    have bodyWellTyped :
        HasType (.extend typingContext (.sort 0)) (.sort 0) (.sort 1) :=
      .sort (.extend .empty domainWellTyped) 0
    simpa only [typingContext, term, domain, body, sourceType] using
      HasType.lam domainWellTyped bodyWellTyped
  have termSequent : RawSequent context term term' termRelation := by
    have bodySequent : RawSequent context.extend
        ((.sort 0 : Term 1).rename originalBinderRenaming)
        ((.sort 0 : Term 1).rename primedBinderRenaming)
        (sortRelation 0 3) := by
      simpa only [Term.rename] using RawSequent.paramSort context.extend 0
    simpa only [term, term', termRelation, domain, body] using
      (RawSequent.paramLam
        (domain := domain)
        (primedDomain := primedDomain)
        (witnessDomain := (.sort 0 : Term 2))
        bodySequent)
  have typeSequent :
      RawSequent context sourceType sourceType typeRelation := by
    have domainSequent : RawSequent context (.sort 0) (.sort 0)
        (sortRelation 0 0) :=
      RawSequent.paramSort context 0
    have codomainSequent : RawSequent context.extend
        ((.sort 1 : Term 1).rename originalBinderRenaming)
        ((.sort 1 : Term 1).rename primedBinderRenaming)
        (sortRelation 1 3) := by
      simpa only [Term.rename] using RawSequent.paramSort context.extend 1
    simpa only [sourceType, typeRelation] using
      RawSequent.paramPi domainSequent codomainSequent
  have primedWellTyped : HasType typingContext term' sourceType :=
    (abstraction admissible sourceWellTyped termSequent typeSequent).1
  obtain ⟨codomain, _bodyWellTyped, productLower⟩ :=
    primedWellTyped.lam_principal
  have erasedProducts := productLower.eraseUniverseLevels
  have erasedDomains := erasedProducts.pi_components.1
  have impossible : Convertible
      (.pi (.sort 0) (.var 0) : Term 0) (.sort 0) := by
    simpa only [primedDomain, sourceType, Term.eraseUniverseLevels] using
      erasedDomains
  exact impossible.symm.sort_not_pi

example : ¬ RawAbstractionClaim := not_rawAbstractionClaim

end DeepWiki.Refine.DependentCalculus.ParametricitySequents
