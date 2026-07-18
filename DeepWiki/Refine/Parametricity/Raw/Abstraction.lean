import DeepWiki.Refine.Parametricity.Raw.AbstractionClaims
import DeepWiki.Refine.Parametricity.Raw.FormationTyping
import DeepWiki.Refine.Parametricity.Raw.RelationalCumulativity

/-! # Raw abstraction

The structural induction over formation-explicit typing proves witness abstraction, from which
the ordinary and displayed raw abstraction theorems follow.
-/

namespace DeepWiki.Refine.DependentCalculus.RawParametricity

namespace FormationHasType

/-- Formation-explicit typing yields translated-context formation and witness typing together. -/
theorem structural {source : Context n} {term type : Term n}
    (termWellTyped : FormationHasType source term type) :
    WellFormed (context source) ∧
      HasType (context source) (translate term) (relatedTermType term type) := by
  refine FormationHasType.rec
    (motive_1 := fun source _ => WellFormed (context source))
    (motive_2 := fun source term type _ =>
      WellFormed (context source) ∧
        HasType (context source) (translate term) (relatedTermType term type))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ termWellTyped
  · exact context_empty_wellFormed
  · intro _ _ _ _ _ typeWellTyped sourceInduction typeInduction
    exact context_extend_wellFormed sourceInduction typeWellTyped.erase typeInduction.2
  · intro _ _ _ level sourceInduction
    exact ⟨sourceInduction, translate_sort_witness_hasType sourceInduction level⟩
  · intro _ _ _ index sourceInduction
    exact ⟨sourceInduction, translate_var_witness_hasType sourceInduction index⟩
  · intro _ _ _ _ _ _ functionWellTyped argumentWellTyped
      functionInduction argumentInduction
    exact ⟨functionInduction.1,
      translate_app_witness_hasType functionInduction.1
        functionWellTyped.erase argumentWellTyped.erase
        functionInduction.2 argumentInduction.2⟩
  · intro _ source domain body codomain domainLevel codomainLevel
      domainWellTyped codomainWellTyped bodyWellTyped
      domainInduction codomainInduction bodyInduction
    have productWellTyped :
        HasType source (.pi domain codomain)
          (.sort (max domainLevel codomainLevel)) :=
      .pi domainWellTyped.erase codomainWellTyped.erase
    have productWitness := translate_pi_witness_hasType
      domainInduction.1 domainWellTyped.erase codomainWellTyped.erase
      domainInduction.2 codomainInduction.2
    exact ⟨domainInduction.1,
      translate_lam_witness_hasType_of_productWitness
        domainInduction.1 domainWellTyped.erase bodyWellTyped.erase
        productWellTyped productWitness bodyInduction.2⟩
  · intro _ _ _ _ _ _ domainWellTyped codomainWellTyped
      domainInduction codomainInduction
    exact ⟨domainInduction.1,
      translate_pi_witness_hasType domainInduction.1
        domainWellTyped.erase codomainWellTyped.erase
        domainInduction.2 codomainInduction.2⟩
  · intro _ _ _ _ _ _ termWellTyped targetWellTyped equal
      termInduction targetInduction
    exact ⟨termInduction.1,
      translate_conversion_witness_hasType termInduction.1
        termWellTyped.erase targetWellTyped.erase equal
        termInduction.2 targetInduction.2⟩
  · intro _ source term _ type' _ termWellTyped targetWellTyped
      subtype termInduction targetInduction
    have raisedTerm : HasType source term type' :=
      .cumulativity termWellTyped.erase targetWellTyped.erase subtype
    exact ⟨termInduction.1,
      .cumulativity termInduction.2
        (relatedTermType_hasType_of_typeWitness termInduction.1 raisedTerm
          targetWellTyped.erase targetInduction.2)
        (IsRelationallyCumulative.apply
          (isRelationallyCumulative_of_cumulative subtype) term)⟩

/-- Every formation-explicit typing derivation satisfies raw witness abstraction. -/
theorem witness {source : Context n} {term type : Term n}
    (termWellTyped : FormationHasType source term type) :
    HasType (context source) (translate term) (relatedTermType term type) :=
  termWellTyped.structural.2

/-- Every formation-explicit typing derivation forms its translated context. -/
theorem translatedContextWellFormed {source : Context n} {term type : Term n}
    (termWellTyped : FormationHasType source term type) :
    WellFormed (context source) :=
  termWellTyped.structural.1

end FormationHasType

/-- Formation-explicit typing proves all three displayed raw abstraction conclusions. -/
theorem abstractionConclusion_of_formationHasType {source : Context n}
    {term type : Term n} (termWellTyped : FormationHasType source term type) :
    AbstractionConclusion source term type := by
  have translatedWellFormed :=
    termWellTyped.translatedContextWellFormed
  exact ⟨HasType.original termWellTyped.erase translatedWellFormed,
    HasType.primed termWellTyped.erase translatedWellFormed,
    termWellTyped.witness⟩

/-- The displayed abstraction claim restricted to formation-explicit typing derivations. -/
def FormationExplicitRawAbstractionClaim : Prop :=
  ∀ {n : Nat} {source : Context n} {term type : Term n},
    FormationHasType source term type → AbstractionConclusion source term type

/-- Formation-explicit dependent typing satisfies the displayed raw abstraction theorem. -/
theorem formationExplicitRawAbstraction : FormationExplicitRawAbstractionClaim :=
  fun termWellTyped => abstractionConclusion_of_formationHasType termWellTyped

/-- Ordinary `CCω` typing satisfies raw abstraction. -/
theorem rawAbstraction : RawAbstractionClaim := fun termWellTyped => by
  have formationTyping :=
    FormationHasType.ofHasType termWellTyped
  exact ⟨formationTyping.translatedContextWellFormed,
    abstractionConclusion_of_formationHasType formationTyping⟩

/-- Ordinary `CCω` typing satisfies the displayed raw abstraction theorem. -/
theorem displayedRawAbstraction : DisplayedRawAbstractionClaim :=
  fun termWellTyped => (rawAbstraction termWellTyped).2

example :
    FormationHasType Context.empty (.sort 0 : Term 0) (.sort 2) :=
  .cumulativity (.sort .empty 0) (.sort .empty 2)
    (.sort (by omega))

example {source : Context n} {term type : Term n}
    (termWellTyped : FormationHasType source term type) :
    AbstractionConclusion source term type :=
  formationExplicitRawAbstraction termWellTyped

example : RawAbstractionClaim :=
  rawAbstraction

example : DisplayedRawAbstractionClaim :=
  displayedRawAbstraction

end DeepWiki.Refine.DependentCalculus.RawParametricity
