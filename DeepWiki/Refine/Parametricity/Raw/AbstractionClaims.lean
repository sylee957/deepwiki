import DeepWiki.Refine.Parametricity.Raw.Typing

/-! # Raw abstraction claims

The displayed, full, and structural formulations isolate the conclusions proved by raw abstraction.
-/

namespace DeepWiki.Refine.DependentCalculus.RawParametricity

open DeepWiki.Refine.CCOmega.SurfaceSyntax

/-- The three typing conclusions of raw parametricity abstraction. -/
def AbstractionConclusion (source : Context n) (term type : Term n) : Prop :=
  HasType (context source) (original term) (original type) ∧
    HasType (context source) (primed term) (primed type) ∧
      HasType (context source) (translate term) (relatedTermType term type)

/-- The displayed raw abstraction claim consists exactly of its three typing conclusions. -/
def DisplayedRawAbstractionClaim : Prop :=
  ∀ {n : Nat} {source : Context n} {term type : Term n},
    HasType source term type → AbstractionConclusion source term type

/-- The full scoped raw abstraction statement, including well-formedness of the translated context. -/
def RawAbstractionClaim : Prop :=
  ∀ {n : Nat} {source : Context n} {term type : Term n},
    HasType source term type →
      WellFormed (context source) ∧ AbstractionConclusion source term type

/-- The structural core combines translated-context formation with witness typing. -/
def StructuralAbstractionClaim : Prop :=
  ∀ {n : Nat} {source : Context n} {term type : Term n},
    HasType source term type →
      WellFormed (context source) ∧
        HasType (context source) (translate term) (relatedTermType term type)

/-- Raw abstraction is equivalent to its translated-context and witness-typing core. -/
theorem rawAbstractionClaim_iff_structural :
    RawAbstractionClaim ↔ StructuralAbstractionClaim := by
  constructor
  · intro abstraction n source term type termWellTyped
    obtain ⟨translatedWellFormed, _, _, witnessWellTyped⟩ := abstraction termWellTyped
    exact ⟨translatedWellFormed, witnessWellTyped⟩
  · intro structural n source term type termWellTyped
    obtain ⟨translatedWellFormed, witnessWellTyped⟩ := structural termWellTyped
    exact ⟨translatedWellFormed,
      HasType.original termWellTyped translatedWellFormed,
      HasType.primed termWellTyped translatedWellFormed,
      witnessWellTyped⟩

/-- The explicit context-formation conjunct is equivalent to the displayed abstraction claim. -/
theorem rawAbstractionClaim_iff_displayed :
    RawAbstractionClaim ↔ DisplayedRawAbstractionClaim := by
  constructor
  · intro abstraction n source term type termWellTyped
    exact (abstraction termWellTyped).2
  · intro abstraction n source term type termWellTyped
    have conclusion := abstraction termWellTyped
    exact ⟨HasType.contextWellFormed conclusion.1, conclusion⟩

/-- The displayed abstraction claim reduces to translated-context formation and witness typing. -/
theorem displayedRawAbstractionClaim_iff_structural :
    DisplayedRawAbstractionClaim ↔ StructuralAbstractionClaim :=
  rawAbstractionClaim_iff_displayed.symm.trans rawAbstractionClaim_iff_structural

example : RawAbstractionClaim ↔ StructuralAbstractionClaim :=
  rawAbstractionClaim_iff_structural

example : DisplayedRawAbstractionClaim ↔ StructuralAbstractionClaim :=
  displayedRawAbstractionClaim_iff_structural

end DeepWiki.Refine.DependentCalculus.RawParametricity
