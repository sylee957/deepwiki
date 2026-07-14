import DeepWiki.Refine.RelationStructure

/-! # Dependency requirements

Finite requirement functions for dependent products and non-dependent arrows over relation
annotations, reconstructed from their one-sided tables by variance symmetry. -/

namespace DeepWiki.Refine

/-- The domain level required by a dependent product for one output direction. -/
def MapLevel.piDomainRequirement : MapLevel → MapLevel
  | .zero => .zero
  | .one => .twoA
  | .twoA => .four
  | .twoB => .twoA
  | .three => .four
  | .four => .four

/-- The domain level required by a non-dependent arrow for one output direction. -/
def MapLevel.arrowDomainRequirement : MapLevel → MapLevel
  | .zero => .zero
  | .one => .one
  | .twoA => .twoB
  | .twoB => .twoA
  | .three => .three
  | .four => .four

/-- Reconstruct bidirectional domain and codomain requirements from a one-sided domain table. -/
def reconstructRequirements (domainRequirement : MapLevel → MapLevel)
    (γ : Annotation) : Annotation × Annotation :=
  (⟨domainRequirement γ.backward, domainRequirement γ.forward⟩, γ)

/-- Domain and codomain annotations used to construct a dependent-product relation. -/
def dependentProductRequirements (γ : Annotation) : Annotation × Annotation :=
  reconstructRequirements MapLevel.piDomainRequirement γ

/-- Domain and codomain annotations used to construct a non-dependent arrow relation. -/
def arrowRequirements (γ : Annotation) : Annotation × Annotation :=
  reconstructRequirements MapLevel.arrowDomainRequirement γ

/-- The full dependent-product table is reconstructed by swapping its two one-sided rows. -/
@[simp] theorem dependentProductRequirements_apply (m n : MapLevel) :
    dependentProductRequirements ⟨m, n⟩ =
      (⟨n.piDomainRequirement, m.piDomainRequirement⟩, ⟨m, n⟩) :=
  rfl

/-- The full arrow table is reconstructed by swapping its two one-sided rows. -/
@[simp] theorem arrowRequirements_apply (m n : MapLevel) :
    arrowRequirements ⟨m, n⟩ =
      (⟨n.arrowDomainRequirement, m.arrowDomainRequirement⟩, ⟨m, n⟩) :=
  rfl

/-- The dependent-product requirements for `(m, 0)` reproduce its one-sided table row. -/
theorem dependentProductRequirements_zeroBackward (m : MapLevel) :
    dependentProductRequirements ⟨m, .zero⟩ =
      (⟨.zero, m.piDomainRequirement⟩, ⟨m, .zero⟩) :=
  rfl

/-- The arrow requirements for `(m, 0)` reproduce its one-sided table row. -/
theorem arrowRequirements_zeroBackward (m : MapLevel) :
    arrowRequirements ⟨m, .zero⟩ =
      (⟨.zero, m.arrowDomainRequirement⟩, ⟨m, .zero⟩) :=
  rfl

/-- Dependent-product construction preserves the requested annotation on its codomain. -/
theorem dependentProductRequirements_codomain (γ : Annotation) :
    (dependentProductRequirements γ).2 = γ :=
  rfl

/-- Arrow construction preserves the requested annotation on its codomain. -/
theorem arrowRequirements_codomain (γ : Annotation) :
    (arrowRequirements γ).2 = γ :=
  rfl

/-- Dependent products and arrows have genuinely different requirement functions. -/
theorem dependentProductRequirements_ne_arrowRequirements :
    dependentProductRequirements ≠ arrowRequirements := by
  intro h
  have hrow := congrFun h (Annotation.mk .one .zero)
  cases hrow

example :
    dependentProductRequirements ⟨.zero, .zero⟩ =
      (⟨.zero, .zero⟩, ⟨.zero, .zero⟩) :=
  rfl

example :
    dependentProductRequirements ⟨.one, .zero⟩ =
      (⟨.zero, .twoA⟩, ⟨.one, .zero⟩) :=
  rfl

example :
    dependentProductRequirements ⟨.twoA, .zero⟩ =
      (⟨.zero, .four⟩, ⟨.twoA, .zero⟩) :=
  rfl

example :
    dependentProductRequirements ⟨.twoB, .zero⟩ =
      (⟨.zero, .twoA⟩, ⟨.twoB, .zero⟩) :=
  rfl

example :
    dependentProductRequirements ⟨.three, .zero⟩ =
      (⟨.zero, .four⟩, ⟨.three, .zero⟩) :=
  rfl

example :
    dependentProductRequirements ⟨.four, .zero⟩ =
      (⟨.zero, .four⟩, ⟨.four, .zero⟩) :=
  rfl

example :
    arrowRequirements ⟨.zero, .zero⟩ =
      (⟨.zero, .zero⟩, ⟨.zero, .zero⟩) :=
  rfl

example :
    arrowRequirements ⟨.one, .zero⟩ =
      (⟨.zero, .one⟩, ⟨.one, .zero⟩) :=
  rfl

example :
    arrowRequirements ⟨.twoA, .zero⟩ =
      (⟨.zero, .twoB⟩, ⟨.twoA, .zero⟩) :=
  rfl

example :
    arrowRequirements ⟨.twoB, .zero⟩ =
      (⟨.zero, .twoA⟩, ⟨.twoB, .zero⟩) :=
  rfl

example :
    arrowRequirements ⟨.three, .zero⟩ =
      (⟨.zero, .three⟩, ⟨.three, .zero⟩) :=
  rfl

example :
    arrowRequirements ⟨.four, .zero⟩ =
      (⟨.zero, .four⟩, ⟨.four, .zero⟩) :=
  rfl

example :
    dependentProductRequirements ⟨.twoA, .twoB⟩ =
      (⟨.twoA, .four⟩, ⟨.twoA, .twoB⟩) :=
  rfl

example :
    arrowRequirements ⟨.twoA, .twoB⟩ =
      (⟨.twoA, .twoB⟩, ⟨.twoA, .twoB⟩) :=
  rfl

end DeepWiki.Refine
