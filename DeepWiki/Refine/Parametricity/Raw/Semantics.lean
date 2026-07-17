import DeepWiki.Refine.Dependent

/-! # Semantic raw parametricity

Raw universes are arbitrary proof-relevant heterogeneous relations. Dependent products reuse the
generic `DependentRespectful` relation. -/

namespace DeepWiki.Refine

universe u v w

/-- A raw universe interpretation is an arbitrary proof-relevant heterogeneous relation. -/
abbrev RawUniverseRelation (A : Type u) (B : Type v) := A → B → Type w

/-- The raw translation of a universe is itself a relation between types in the next universe. -/
def rawUniverseTranslation : RawUniverseRelation (Type u) (Type u) :=
  fun A B => A → B → Type u

/-- Applying the raw universe translation returns the type of heterogeneous relations. -/
theorem rawUniverseTranslation_apply (A B : Type u) :
    rawUniverseTranslation A B = (A → B → Type u) :=
  rfl

example (A B : Type u) : rawUniverseTranslation A B = (A → B → Type u) :=
  rawUniverseTranslation_apply A B

end DeepWiki.Refine
