import DeepWiki.Refine.ArrowRelationStructure
import DeepWiki.Refine.PiRelationStructure

/-! # Dependency-feature minimality

Finite feature specifications distinguish least constructor constraints from semantic minimality.
The native respectful-arrow constructor exposes the proof-irrelevance reduction at output level
`4` without asserting impossibility results for still weaker inputs.
-/

namespace DeepWiki.Refine

universe u v u' v' w w'

/-- A named piece of one-direction map-class data consumed by a relation constructor. -/
inductive MapFeature where
  /-- No structure beyond the underlying relation. -/
  | bareRelation
  /-- An otherwise unconstrained map. -/
  | map
  /-- A proof that the map graph implies the relation. -/
  | graphToRel
  /-- A proof that the relation implies the map graph. -/
  | relToGraph
  /-- Both graph-to-relation and relation-to-graph implications. -/
  | bidirectional
  /-- Bidirectional graph data with proof-relevant round-trip coherence. -/
  | coherent
  deriving DecidableEq, Repr

namespace MapFeature

/-- The least map level that contains a named feature package. -/
def minimum : MapFeature → MapLevel
  | .bareRelation => .zero
  | .map => .one
  | .graphToRel => .twoA
  | .relToGraph => .twoB
  | .bidirectional => .three
  | .coherent => .four

/-- A map level provides a feature when it lies above the feature's least level. -/
def ProvidedBy (feature : MapFeature) (level : MapLevel) : Prop :=
  feature.minimum ≤ level

end MapFeature

/-- A level satisfies a consumption specification when it provides every consumed feature. -/
def SatisfiesFeatureSpecification (level : MapLevel)
    (consumes : MapFeature → Prop) : Prop :=
  ∀ feature, consumes feature → feature.ProvidedBy level

/-- A level is the least solution of a finite feature-consumption specification. -/
def IsLeastFeatureSolution (level : MapLevel)
    (consumes : MapFeature → Prop) : Prop :=
  SatisfiesFeatureSpecification level consumes ∧
    ∀ candidate, SatisfiesFeatureSpecification candidate consumes → level ≤ candidate

/-- Every singleton feature specification is solved minimally by that feature's minimum level. -/
theorem MapFeature.minimum_isLeast (feature : MapFeature) :
    IsLeastFeatureSolution feature.minimum (fun consumed => consumed = feature) := by
  constructor
  · intro consumed consumedEqual
    cases consumedEqual
    exact le_rfl
  · intro candidate satisfies
    exact satisfies feature rfl

/-- The one-sided dependent-product constructor's consumed domain feature at each output level. -/
def MapLevel.piDomainFeature : MapLevel → MapFeature
  | .zero => .bareRelation
  | .one => .graphToRel
  | .twoA => .coherent
  | .twoB => .graphToRel
  | .three => .coherent
  | .four => .coherent

/-- The coherence-preserving arrow constructor's consumed domain feature at each output level. -/
def MapLevel.arrowCoherentDomainFeature : MapLevel → MapFeature
  | .zero => .bareRelation
  | .one => .map
  | .twoA => .relToGraph
  | .twoB => .graphToRel
  | .three => .bidirectional
  | .four => .coherent

/-- The native arrow constructor replaces level-`4` domain coherence by bidirectional graph data. -/
def MapLevel.arrowNativeDomainFeature : MapLevel → MapFeature
  | .zero => .bareRelation
  | .one => .map
  | .twoA => .relToGraph
  | .twoB => .graphToRel
  | .three => .bidirectional
  | .four => .bidirectional

/-- Dependent-product feature minima compute the one-sided domain requirements. -/
@[simp] theorem MapLevel.piDomainFeature_minimum (output : MapLevel) :
    output.piDomainFeature.minimum = output.piDomainRequirement := by
  cases output <;> rfl

/-- Coherence-preserving arrow feature minima compute the one-sided domain requirements. -/
@[simp] theorem MapLevel.arrowCoherentDomainFeature_minimum (output : MapLevel) :
    output.arrowCoherentDomainFeature.minimum = output.arrowDomainRequirement := by
  cases output <;> rfl

/-- Native Lean's one-sided arrow requirement lowers only output level `4` from `4` to `3`. -/
def MapLevel.arrowNativeDomainRequirement (output : MapLevel) : MapLevel :=
  output.arrowNativeDomainFeature.minimum

/-- Native arrow feature minima compute the native one-sided requirement table. -/
@[simp] theorem MapLevel.arrowNativeDomainFeature_minimum (output : MapLevel) :
    output.arrowNativeDomainFeature.minimum = output.arrowNativeDomainRequirement :=
  rfl

/-- Every dependent-product requirement is least for its explicit constructor-feature constraint. -/
theorem MapLevel.piDomainRequirement_constraintLeast (output : MapLevel) :
    IsLeastFeatureSolution output.piDomainRequirement
      (fun feature => feature = output.piDomainFeature) := by
  simpa only [MapLevel.piDomainFeature_minimum] using
    MapFeature.minimum_isLeast output.piDomainFeature

/-- Every arrow requirement is least for its coherence-preserving constructor-feature constraint. -/
theorem MapLevel.arrowDomainRequirement_coherentConstraintLeast (output : MapLevel) :
    IsLeastFeatureSolution output.arrowDomainRequirement
      (fun feature => feature = output.arrowCoherentDomainFeature) := by
  simpa only [MapLevel.arrowCoherentDomainFeature_minimum] using
    MapFeature.minimum_isLeast output.arrowCoherentDomainFeature

/-- Every native arrow row is least for its explicit native constructor-feature constraint. -/
theorem MapLevel.arrowNativeDomainRequirement_constraintLeast (output : MapLevel) :
    IsLeastFeatureSolution output.arrowNativeDomainRequirement
      (fun feature => feature = output.arrowNativeDomainFeature) := by
  simpa only [MapLevel.arrowNativeDomainFeature_minimum] using
    MapFeature.minimum_isLeast output.arrowNativeDomainFeature

/-- Away from output level `4`, the coherence-preserving and native arrow constraints coincide. -/
theorem MapLevel.arrowDomainRequirement_eq_native_of_ne_four
    {output : MapLevel} (notFour : output ≠ .four) :
    output.arrowDomainRequirement = output.arrowNativeDomainRequirement := by
  cases output <;> simp_all [MapLevel.arrowDomainRequirement,
    MapLevel.arrowNativeDomainRequirement, MapLevel.arrowNativeDomainFeature,
    MapFeature.minimum]

/-- Every coherence-preserving arrow requirement below `4` is least for the native constraint. -/
theorem MapLevel.arrowDomainRequirement_nativeConstraintLeast_of_ne_four
    {output : MapLevel} (notFour : output ≠ .four) :
    IsLeastFeatureSolution output.arrowDomainRequirement
      (fun feature => feature = output.arrowNativeDomainFeature) := by
  rw [output.arrowDomainRequirement_eq_native_of_ne_four notFour]
  exact output.arrowNativeDomainRequirement_constraintLeast

/-- The coherence-preserving output-`4` arrow requirement satisfies the native constraint. -/
theorem arrowFour_coherentRequirement_satisfies_nativeConstraint :
    SatisfiesFeatureSpecification MapLevel.four
      (fun feature => feature = MapLevel.four.arrowNativeDomainFeature) := by
  intro feature featureEqual
  cases featureEqual
  change MapLevel.three ≤ MapLevel.four
  decide

/-- The coherence-preserving output-`4` arrow requirement is not least for the native constraint. -/
theorem arrowFour_coherentRequirement_not_nativeConstraintLeast :
    ¬ IsLeastFeatureSolution MapLevel.four
      (fun feature => feature = MapLevel.four.arrowNativeDomainFeature) := by
  intro least
  have lowerSatisfies :
      SatisfiesFeatureSpecification MapLevel.three
        (fun feature => feature = MapLevel.four.arrowNativeDomainFeature) := by
    intro feature featureEqual
    cases featureEqual
    exact le_rfl
  have impossible : MapLevel.four ≤ MapLevel.three := least.2 _ lowerSatisfies
  have notLe : ¬ MapLevel.four ≤ MapLevel.three := by decide
  exact notLe impossible

/-- Indexed native arrow construction implements the UIP-reduced domain requirement table. -/
def MapClass.arrowNative {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'} {level : MapLevel}
    (domain : MapClass (Converse R) level.arrowNativeDomainRequirement)
    (codomain : MapClass S level) : MapClass (ArrowRelation R S) level := by
  cases level with
  | zero => exact .zero
  | one =>
      cases domain with
      | one domain =>
          cases codomain with
          | one codomain => exact .one (ArrowRelation.mapClass1 domain codomain)
  | twoA =>
      cases domain with
      | twoB domain =>
          cases codomain with
          | twoA codomain => exact .twoA (ArrowRelation.mapClass2a domain codomain)
  | twoB =>
      cases domain with
      | twoA domain =>
          cases codomain with
          | twoB codomain => exact .twoB (ArrowRelation.mapClass2b domain codomain)
  | three =>
      cases domain with
      | three domain =>
          cases codomain with
          | three codomain => exact .three (ArrowRelation.mapClass3 domain codomain)
  | four =>
      cases domain with
      | three domain =>
          cases codomain with
          | four codomain => exact .four (ArrowRelation.mapClass4OfDomain3 domain codomain)

/-- A domain level is universally sufficient for constructing output-level-`4` arrow data. -/
def ArrowLevelFourSufficient (domainLevel : MapLevel) : Prop :=
  Nonempty
    (∀ {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
      {R : A → B → Sort w} {S : C → D → Sort w'},
      MapClass (Converse R) domainLevel → MapClass4 S →
        MapClass4 (ArrowRelation R S))

/-- Native proof irrelevance makes domain level `3` sufficient for arrow output level `4`. -/
theorem arrowLevelFourSufficient_three :
    ArrowLevelFourSufficient.{u, v, u', v', w, w'} MapLevel.three :=
  ⟨fun domain codomain => by
    cases domain with
    | three domain => exact ArrowRelation.mapClass4OfDomain3 domain codomain⟩

/-- A proposed level is least sufficient when it is sufficient and below every sufficient level. -/
def IsLeastSufficientLevel (level : MapLevel) (sufficient : MapLevel → Prop) : Prop :=
  sufficient level ∧ ∀ candidate, sufficient candidate → level ≤ candidate

/-- The coherence-preserving level-`4` arrow requirement is not semantically least in native Lean. -/
theorem arrowFour_coherentRequirement_not_nativeSemanticallyLeast :
    ¬ IsLeastSufficientLevel MapLevel.four
      (ArrowLevelFourSufficient.{u, v, u', v', w, w'}) := by
  intro least
  have impossible : MapLevel.four ≤ MapLevel.three :=
    least.2 MapLevel.three arrowLevelFourSufficient_three
  have notLe : ¬ MapLevel.four ≤ MapLevel.three := by decide
  exact notLe impossible

example (output : MapLevel) :
    IsLeastFeatureSolution output.piDomainRequirement
      (fun feature => feature = output.piDomainFeature) :=
  output.piDomainRequirement_constraintLeast

example (output : MapLevel) :
    IsLeastFeatureSolution output.arrowDomainRequirement
      (fun feature => feature = output.arrowCoherentDomainFeature) :=
  output.arrowDomainRequirement_coherentConstraintLeast

example : MapLevel.four.arrowDomainRequirement = MapLevel.four :=
  rfl

example : MapLevel.four.arrowNativeDomainRequirement = MapLevel.three :=
  rfl

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (domain : MapClass3 (Converse R)) (codomain : MapClass4 S) :
    MapClass4 (ArrowRelation R S) :=
  ArrowRelation.mapClass4OfDomain3 domain codomain

example :
    ¬ IsLeastFeatureSolution MapLevel.four
      (fun feature => feature = MapLevel.four.arrowNativeDomainFeature) :=
  arrowFour_coherentRequirement_not_nativeConstraintLeast

end DeepWiki.Refine
