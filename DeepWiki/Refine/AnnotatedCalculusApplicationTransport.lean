import DeepWiki.Refine.DependentCalculusCumulativeInversion
import DeepWiki.Refine.DependentCalculusRegularity

/-! # Relation-indexed application transport

Application typehood transport retains the erased function-subtyping derivation. Mutual
induction then reduces ordinary conservativity to this constructor-local boundary.
-/

namespace DeepWiki.Refine.AnnotatedCalculusConservativity

/-- Typed conversion between common-kind endpoints preserves universe typehood. -/
theorem typedConversionUniverseRegularity : TypedConversionUniverseRegularity :=
  typedConversionUniverseRegularity_of_assignedKindSortDiscrimination
    assignedKindSortDiscrimination

/-- No lambda abstraction is itself assigned a universe sort. -/
theorem not_isUniverseTyped_lambda
    {context : DependentCalculus.Context n}
    {domain : DependentCalculus.Term n}
    {body : DependentCalculus.Term (n + 1)} :
    ¬ IsUniverseTyped context (.lam domain body) := by
  rintro ⟨level, lambdaWellTyped⟩
  obtain ⟨codomain, _bodyWellTyped, productLower⟩ :=
    lambdaWellTyped.lam_principal
  exact productLower.eraseUniverseLevels.symm.sort_not_pi

/-- Application transport indexed by the function-subtyping derivation of the application rule. -/
structure ErasedSubtypeRelationIndexedApplicationTransport : Prop where
  /-- Forward transport retains both the function subtype and its recursive typehood theorem. -/
  forward : ∀ {n : Nat} {context : UnderlyingDependentCalculus.Context n}
      {function function' argument kind : UnderlyingDependentCalculus.Term n},
    UnderlyingDependentCalculus.Subtype context function function' →
      UnderlyingDependentCalculus.IsKind kind →
      UnderlyingDependentCalculus.HasType context (.app function' argument) kind →
      (IsUniverseTyped context function → IsUniverseTyped context function') →
      IsUniverseTyped context (.app function argument) →
        IsUniverseTyped context (.app function' argument)
  /-- Reverse transport retains both the function subtype and its recursive typehood theorem. -/
  reverse : ∀ {n : Nat} {context : UnderlyingDependentCalculus.Context n}
      {function function' argument kind : UnderlyingDependentCalculus.Term n},
    UnderlyingDependentCalculus.Subtype context function function' →
      UnderlyingDependentCalculus.IsKind kind →
      UnderlyingDependentCalculus.HasType context (.app function' argument) kind →
      (IsUniverseTyped context function' → IsUniverseTyped context function) →
      IsUniverseTyped context (.app function' argument) →
        IsUniverseTyped context (.app function argument)

mutual

  /-- Relation-indexed application transport embeds every erased well-formed context. -/
  def underlyingWellFormedToExisting_of_relationIndexedApplicationTransport
      (transport : ErasedSubtypeRelationIndexedApplicationTransport)
      {context : UnderlyingDependentCalculus.Context n} :
      UnderlyingDependentCalculus.WellFormed context →
        DependentCalculus.WellFormed context
    | .empty => .empty
    | .extend contextWellFormed typeWellTyped =>
        .extend
          (underlyingWellFormedToExisting_of_relationIndexedApplicationTransport transport
            contextWellFormed)
          (underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport
            typeWellTyped)

  /-- Relation-indexed application transport embeds every erased typing derivation. -/
  def underlyingHasTypeToExisting_of_relationIndexedApplicationTransport
      (transport : ErasedSubtypeRelationIndexedApplicationTransport)
      {context : UnderlyingDependentCalculus.Context n}
      {term type : UnderlyingDependentCalculus.Term n} :
      UnderlyingDependentCalculus.HasType context term type →
        DependentCalculus.HasType context term type
    | .sort contextWellFormed level =>
        .sort
          (underlyingWellFormedToExisting_of_relationIndexedApplicationTransport transport
            contextWellFormed) level
    | .var contextWellFormed index =>
        .var
          (underlyingWellFormedToExisting_of_relationIndexedApplicationTransport transport
            contextWellFormed) index
    | .app functionWellTyped argumentWellTyped =>
        .app
          (underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport
            functionWellTyped)
          (underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport
            argumentWellTyped)
    | .lam bodyWellTyped => by
        have bodyExisting :=
          underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport
            bodyWellTyped
        cases bodyExisting.contextWellFormed with
        | extend _ domainWellTyped =>
            exact .lam domainWellTyped bodyExisting
    | .arrow domainWellTyped codomainWellTyped => by
        have domainExisting :=
          underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport
            domainWellTyped
        have codomainExisting :=
          underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport
            codomainWellTyped
        have extendedWellFormed :
            DependentCalculus.WellFormed (.extend context _) :=
          .extend domainExisting.contextWellFormed domainExisting
        simpa only [UnderlyingDependentCalculus.Term.arrow, Nat.max_self] using
          DependentCalculus.HasType.pi domainExisting
            (codomainExisting.weaken extendedWellFormed)
    | .pi domainWellTyped codomainWellTyped => by
        have domainExisting :=
          underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport
            domainWellTyped
        have codomainExisting :=
          underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport
            codomainWellTyped
        simpa only [Nat.max_self] using
          DependentCalculus.HasType.pi domainExisting codomainExisting
    | .conversion termWellTyped subtype => by
        have termExisting :=
          underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport
            termWellTyped
        obtain ⟨_, targetWellTyped⟩ :=
          subtypeForwardTypehoodOfRelationIndexedApplicationTransport transport subtype
            termExisting.typeWellTyped
        exact .cumulativity termExisting targetWellTyped (subtype_toCumulative subtype)

  /-- Relation-indexed application transport carries typehood forward through erased subtyping. -/
  def subtypeForwardTypehoodOfRelationIndexedApplicationTransport
      (transport : ErasedSubtypeRelationIndexedApplicationTransport)
      {context : UnderlyingDependentCalculus.Context n}
      {left right : UnderlyingDependentCalculus.Term n}
      (derivation : UnderlyingDependentCalculus.Subtype context left right) :
      IsUniverseTyped context left → IsUniverseTyped context right :=
    match derivation with
    | .conversion kindShape leftWellTyped rightWellTyped equal =>
        typedConversionUniverseRegularity kindShape
          (underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport
            leftWellTyped)
          (underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport
            rightWellTyped)
          equal
    | .sort _ => fun leftWellTyped =>
        ⟨_, .sort (Exists.choose_spec leftWellTyped).contextWellFormed _⟩
    | .app kindShape targetWellTyped functionSubtype =>
        transport.forward functionSubtype kindShape targetWellTyped
          (subtypeForwardTypehoodOfRelationIndexedApplicationTransport transport
            functionSubtype)
    | .lam _bodySubtype => fun lambdaWellTyped =>
        (not_isUniverseTyped_lambda lambdaWellTyped).elim
    | .pi _productWellTyped domainSubtype codomainSubtype => fun productWellTyped =>
        piUniverseTyped_of_transport (subtype_toCumulative domainSubtype)
          (subtypeReverseTypehoodOfRelationIndexedApplicationTransport transport
            domainSubtype)
          (subtypeForwardTypehoodOfRelationIndexedApplicationTransport transport
            codomainSubtype)
          productWellTyped

  /-- Relation-indexed application transport carries typehood backward through erased subtyping. -/
  def subtypeReverseTypehoodOfRelationIndexedApplicationTransport
      (transport : ErasedSubtypeRelationIndexedApplicationTransport)
      {context : UnderlyingDependentCalculus.Context n}
      {left right : UnderlyingDependentCalculus.Term n}
      (derivation : UnderlyingDependentCalculus.Subtype context left right) :
      IsUniverseTyped context right → IsUniverseTyped context left :=
    match derivation with
    | .conversion kindShape leftWellTyped rightWellTyped equal =>
        typedConversionUniverseRegularity kindShape
          (underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport
            rightWellTyped)
          (underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport
            leftWellTyped)
          equal.symm
    | .sort _ => fun rightWellTyped =>
        ⟨_, .sort (Exists.choose_spec rightWellTyped).contextWellFormed _⟩
    | .app kindShape targetWellTyped functionSubtype =>
        transport.reverse functionSubtype kindShape targetWellTyped
          (subtypeReverseTypehoodOfRelationIndexedApplicationTransport transport
            functionSubtype)
    | .lam _bodySubtype => fun lambdaWellTyped =>
        (not_isUniverseTyped_lambda lambdaWellTyped).elim
    | .pi productWellTyped _domainSubtype _codomainSubtype => fun _rightWellTyped =>
        ⟨_, underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport
          productWellTyped⟩

end

/-- Relation-indexed application transport proves exact erased-subtyping typehood. -/
theorem erasedSubtypeTypehood_of_relationIndexedApplicationTransport
    (transport : ErasedSubtypeRelationIndexedApplicationTransport) :
    ErasedSubtypeTypehood := by
  intro n context left right leftWellTyped subtype
  exact subtypeForwardTypehoodOfRelationIndexedApplicationTransport transport subtype
    leftWellTyped

/-- Relation-indexed application transport gives the complete erased-calculus embedding. -/
def existingCalculusEmbedding_of_relationIndexedApplicationTransport
    (transport : ErasedSubtypeRelationIndexedApplicationTransport) :
    ExistingCalculusEmbedding where
  wellFormed :=
    underlyingWellFormedToExisting_of_relationIndexedApplicationTransport transport
  hasType := underlyingHasTypeToExisting_of_relationIndexedApplicationTransport transport

/-- Relation-indexed application transport proves repaired typing conservativity. -/
theorem existingTypingConservativity_of_relationIndexedApplicationTransport
    (transport : ErasedSubtypeRelationIndexedApplicationTransport) :
    ExistingTypingConservativity :=
  existingTypingConservativity_of_embedding
    (existingCalculusEmbedding_of_relationIndexedApplicationTransport transport)

example (transport : ErasedSubtypeRelationIndexedApplicationTransport) :
    ExistingTypingConservativity :=
  existingTypingConservativity_of_relationIndexedApplicationTransport transport

end DeepWiki.Refine.AnnotatedCalculusConservativity
