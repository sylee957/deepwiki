import DeepWiki.Refine.TypeEquivalence

/-! # Univalent relation packages

A univalent relation packages a proof-relevant relation, a type equivalence, and coherence with the
equivalence's backward equality graph. -/

namespace DeepWiki.Refine

universe u

noncomputable section

/-- The equality graph of backward transport, lifted into the carrier universe. -/
abbrev BackwardEqualityGraph {A B : Type u} (equivalence : A ≃ B) (a : A) (b : B) :=
  ULift.{u} (PLift (a = equivalence.symm b))

/-- A univalent universe relation packages a relation, an equivalence, and identification of the
relation with the equality graph of backward transport. -/
structure UnivalentRelation (A B : Type u) where
  /-- The type equivalence carried by the universe relation. -/
  equivalence : A ≃ B
  /-- The proof-relevant heterogeneous relation between elements. -/
  relation : A → B → Type u
  /-- Each relation fiber is equivalent to equality after backward transport. -/
  relationEquiv : ∀ a b, relation a b ≃ BackwardEqualityGraph equivalence a b

/-- Two univalent relation packages agree when their equivalences and relation families agree. -/
@[ext] theorem UnivalentRelation.ext {A B : Type u} {left right : UnivalentRelation A B}
    (equivalence_eq : left.equivalence = right.equivalence)
    (relation_eq : left.relation = right.relation) : left = right := by
  cases left with
  | mk leftEquivalence leftRelation leftRelationEquiv =>
    cases right with
    | mk rightEquivalence rightRelation rightRelationEquiv =>
      cases equivalence_eq
      cases relation_eq
      congr
      funext a b
      apply Equiv.ext
      intro witness
      exact Subsingleton.elim _ _

/-- The relation used in a translated typing judgment is the first relational projection of the
univalent universe package. -/
def UnivalentRelation.rel {A B : Type u} (package : UnivalentRelation A B) :
    A → B → Type u :=
  package.relation

/-- Every type equivalence has a canonical univalent relation given by its equality graph. -/
def UnivalentRelation.ofEquiv {A B : Type u} (equivalence : A ≃ B) :
    UnivalentRelation A B where
  equivalence := equivalence
  relation := BackwardEqualityGraph equivalence
  relationEquiv := fun _ _ => Equiv.refl _

/-- Univalence identifies the relation family in a universe package with its equality graph. -/
theorem UnivalentRelation.relation_eq_graph (univalent : IsUnivalentUniverse.{u})
    {A B : Type u} (package : UnivalentRelation A B) :
    package.relation = BackwardEqualityGraph package.equivalence := by
  funext a b
  exact univalent.pathOfEquivalence (package.relationEquiv a b)

/-- Assuming univalence, universe-relation packages are equivalent to ordinary type equivalences. -/
def univalentRelationEquivTypeEquivalence (univalent : IsUnivalentUniverse.{u})
    (A B : Type u) : UnivalentRelation A B ≃ (A ≃ B) where
  toFun := UnivalentRelation.equivalence
  invFun := UnivalentRelation.ofEquiv
  left_inv := fun package => by
    apply UnivalentRelation.ext
    · apply Equiv.ext
      intro a
      rfl
    · exact (package.relation_eq_graph univalent).symm
  right_inv := fun _ => by
    apply Equiv.ext
    intro a
    rfl

/-- Under univalence, the translated universe is itself a well-formed univalent relation package. -/
def univalentUniverseRelation (univalent : IsUnivalentUniverse.{u}) :
    UnivalentRelation (Type u) (Type u) where
  equivalence := Equiv.refl (Type u)
  relation := UnivalentRelation
  relationEquiv := fun A B =>
    (univalentRelationEquivTypeEquivalence univalent A B).trans
      ((univalent A B).toEquiv.symm.trans
        (Equiv.plift.symm.trans Equiv.ulift.symm))

/-- Projecting the translated universe package recovers the univalent relation interpretation. -/
theorem univalentUniverseRelation_rel (univalent : IsUnivalentUniverse.{u}) :
    (univalentUniverseRelation univalent).rel = UnivalentRelation :=
  rfl

example (univalent : IsUnivalentUniverse.{u}) (A B : Type u) :
    UnivalentRelation A B ≃ (A ≃ B) :=
  univalentRelationEquivTypeEquivalence univalent A B

example (univalent : IsUnivalentUniverse.{u}) :
    (univalentUniverseRelation univalent).rel = UnivalentRelation :=
  univalentUniverseRelation_rel univalent

end

end DeepWiki.Refine
