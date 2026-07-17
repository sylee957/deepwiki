import DeepWiki.Refine.AnnotationLattice
import DeepWiki.Refine.FunctionalRelation
import DeepWiki.Refine.RelationEquivalence
import DeepWiki.Refine.UnivalentRelationStructure

/-! # Structured universe relations

Weak universe annotations are populated constructively, while a fully coherent source relation
uses explicit universe-univalence evidence to support every target annotation. -/

namespace DeepWiki.Refine

universe u w

/-- The converse of the identity equality graph carries its canonical coherent identity map. -/
def identityEqualityGraphConverseIsUmap (A : Type u) :
    IsUmap (Converse (EqualityGraph.{u, u, w} (id : A → A))) where
  map := id
  graphToRel := fun _ _ path => ⟨⟨path.symm⟩⟩
  relToGraph := fun _ _ related => related.down.down.symm
  coherent := by
    intro _ _ related
    rcases related with ⟨⟨path⟩⟩
    congr

/-- The identity equality graph at the top annotation, weakened to annotation `α`. -/
def StructuredRelation.refl (α : Annotation) (A : Type u) :
    StructuredRelation.{u, u, w} α A A :=
  StructuredRelation.weaken
    (show α ≤ Annotation.equivalence from ⟨le_top, le_top⟩)
    ⟨EqualityGraph.{u, u, w} (id : A → A),
      .four (equalityGraphIsUmap (id : A → A)),
      .four (identityEqualityGraphConverseIsUmap A)⟩

/-- A reflexive structured relation projects to the lifted identity equality graph. -/
@[simp] theorem StructuredRelation.rel_refl (α : Annotation) (A : Type u) :
    (StructuredRelation.refl.{u, w} α A).rel =
      EqualityGraph.{u, u, w} (id : A → A) :=
  rfl

/-- The structured-relation universe family carries bare forward relation data. -/
def universeStructuredRelationMapClass0 (source : Annotation) :
    MapClass0 (fun A B : Type u => StructuredRelation.{u, u, u} source A B) :=
  ()

/-- The structured-relation universe family carries the identity forward map on types. -/
def universeStructuredRelationMapClass1 (source : Annotation) :
    MapClass1 (fun A B : Type u => StructuredRelation.{u, u, u} source A B) where
  map := id

/-- Type equality produces a reflexive source-structured relation at forward level `2a`. -/
def universeStructuredRelationMapClass2a (source : Annotation) :
    MapClass2a (fun A B : Type u => StructuredRelation.{u, u, u} source A B) where
  map := id
  graphToRel := fun A _ path => path ▸ StructuredRelation.refl source A

/-- The converse structured-relation universe family carries bare relation data. -/
def universeStructuredRelationConverseMapClass0 (source : Annotation) :
    MapClass0
      (Converse (fun A B : Type u => StructuredRelation.{u, u, u} source A B)) :=
  ()

/-- The converse structured-relation universe family carries the identity map on types. -/
def universeStructuredRelationConverseMapClass1 (source : Annotation) :
    MapClass1
      (Converse (fun A B : Type u => StructuredRelation.{u, u, u} source A B)) where
  map := id

/-- Type equality produces a reflexive source-structured relation at backward level `2a`. -/
def universeStructuredRelationConverseMapClass2a (source : Annotation) :
    MapClass2a
      (Converse (fun A B : Type u => StructuredRelation.{u, u, u} source A B)) where
  map := id
  graphToRel := fun A _ path => path ▸ StructuredRelation.refl source A

/-- Assemble forward universe-relation data at any weak directional level. -/
def universeStructuredRelationMapClassOfWeak (source : Annotation) (level : MapLevel)
    (h : level.IsUniverseWeak) :
    MapClass (fun A B : Type u => StructuredRelation.{u, u, u} source A B) level := by
  cases level with
  | zero => exact .zero
  | one => exact .one (universeStructuredRelationMapClass1 source)
  | twoA => exact .twoA (universeStructuredRelationMapClass2a source)
  | twoB => exact False.elim h
  | three => exact False.elim h
  | four => exact False.elim h

/-- Assemble backward universe-relation data at any weak directional level. -/
def universeStructuredRelationConverseMapClassOfWeak (source : Annotation) (level : MapLevel)
    (h : level.IsUniverseWeak) :
    MapClass (Converse (fun A B : Type u => StructuredRelation.{u, u, u} source A B)) level := by
  cases level with
  | zero => exact .zero
  | one => exact .one (universeStructuredRelationConverseMapClass1 source)
  | twoA => exact .twoA (universeStructuredRelationConverseMapClass2a source)
  | twoB => exact False.elim h
  | three => exact False.elim h
  | four => exact False.elim h

/-- Every weak target annotation structures the universe relation of source-structured relations. -/
def universeStructuredRelationOfWeak (source target : Annotation) (h : target.IsUniverseWeak) :
    StructuredRelation.{u + 1, u + 1, u + 1} target (Type u) (Type u) :=
  ⟨fun A B => StructuredRelation.{u, u, u} source A B,
    universeStructuredRelationMapClassOfWeak source target.forward h.1,
    universeStructuredRelationConverseMapClassOfWeak source target.backward h.2⟩

/-- The weak universe witness projects definitionally to the source-structured relation family. -/
@[simp] theorem universeStructuredRelationOfWeak_rel (source target : Annotation)
    (h : target.IsUniverseWeak) :
    (universeStructuredRelationOfWeak source target h).rel =
      (fun A B : Type u => StructuredRelation.{u, u, u} source A B) :=
  rfl

/-- Explicit universe univalence gives the top forward map on top structured relations. -/
def universeStructuredRelationTopForwardIsUmap (univalent : IsUnivalentUniverse.{u}) :
    IsUmap
      (fun A B : Type u =>
        StructuredRelation.{u, u, u} Annotation.equivalence A B) :=
  MapClass4.congr
    (fun A B => univalentRelationEquivStructuredRelationTop A B)
    (univalentUniverseRelation univalent).forwardIsUmap

/-- Explicit universe univalence gives the top backward map on top structured relations. -/
def universeStructuredRelationTopBackwardIsUmap (univalent : IsUnivalentUniverse.{u}) :
    IsUmap
      (Converse (fun A B : Type u =>
        StructuredRelation.{u, u, u} Annotation.equivalence A B)) :=
  MapClass4.congr
    (fun B A => univalentRelationEquivStructuredRelationTop A B)
    (univalentUniverseRelation univalent).backwardIsUmap

/-- Explicit universe univalence structures the top-source universe relation at annotation `4,4`. -/
def universeStructuredRelationTop (univalent : IsUnivalentUniverse.{u}) :
    StructuredRelation.{u + 1, u + 1, u + 1}
      Annotation.equivalence (Type u) (Type u) :=
  ⟨fun A B => StructuredRelation.{u, u, u} Annotation.equivalence A B,
    .four (universeStructuredRelationTopForwardIsUmap univalent),
    .four (universeStructuredRelationTopBackwardIsUmap univalent)⟩

/-- The top universe relation fiber is definitionally the type of top structured relations. -/
@[simp] theorem universeRelationTop_fiber (univalent : IsUnivalentUniverse.{u})
    (A B : Type u) :
    (universeStructuredRelationTop univalent).rel A B =
      StructuredRelation.{u, u, u} Annotation.equivalence A B :=
  rfl

/-- A top universe relation fiber is equivalent to a relation with univalent maps both ways. -/
def universeRelationTopFiberEquiv (univalent : IsUnivalentUniverse.{u})
    (A B : Type u) :
    (universeStructuredRelationTop univalent).rel A B ≃
      BidirectionallyUnivalentRelationData.{u, u, u} A B :=
  (bidirectionallyUnivalentEquivStructuredRelation A B).symm

/-- Every top universe relation fiber has the bidirectionally univalent sigma characterization. -/
theorem universeRelationTopFiber_characterization
    (univalent : IsUnivalentUniverse.{u}) (A B : Type u) :
    Nonempty
      ((universeStructuredRelationTop univalent).rel A B ≃
        (Σ R : A → B → Type u, IsUmap R × IsUmap (Converse R))) :=
  ⟨universeRelationTopFiberEquiv univalent A B⟩

/-- The top universe witness projects to the family of top structured relations. -/
@[simp] theorem universeStructuredRelationTop_rel (univalent : IsUnivalentUniverse.{u}) :
    (universeStructuredRelationTop univalent).rel =
      (fun A B : Type u =>
        StructuredRelation.{u, u, u} Annotation.equivalence A B) :=
  rfl

/-- A top source and explicit universe univalence support every target annotation. -/
def universeStructuredRelationOfTop (univalent : IsUnivalentUniverse.{u})
    (target : Annotation) :
    StructuredRelation.{u + 1, u + 1, u + 1} target (Type u) (Type u) :=
  StructuredRelation.weaken
    (show target ≤ Annotation.equivalence from ⟨le_top, le_top⟩)
    (universeStructuredRelationTop univalent)

/-- Weakening the top universe witness preserves its structured-relation family. -/
@[simp] theorem universeStructuredRelationOfTop_rel (univalent : IsUnivalentUniverse.{u})
    (target : Annotation) :
    (universeStructuredRelationOfTop univalent target).rel =
      (fun A B : Type u =>
        StructuredRelation.{u, u, u} Annotation.equivalence A B) :=
  rfl

/-- Branch-local assumptions needed to construct an admissible structured universe relation. -/
inductive UniverseRelationAssumptions : Annotation → Annotation → Type (u + 1) where
  /-- A weak target requires no univalence evidence. -/
  | weak {source target : Annotation} (targetWeak : target.IsUniverseWeak) :
      UniverseRelationAssumptions source target
  /-- A non-weak target requires a top source and explicit universe univalence. -/
  | strong {target : Annotation} (targetNotWeak : ¬ target.IsUniverseWeak)
      (univalent : IsUnivalentUniverse.{u}) :
      UniverseRelationAssumptions Annotation.equivalence target

/-- Branch-local universe assumptions imply annotation admissibility. -/
theorem UniverseRelationAssumptions.admissible
    {source target : Annotation} :
    UniverseRelationAssumptions.{u} source target →
      AdmissibleUniverseTranslation source target
  | .weak targetWeak => Or.inr targetWeak
  | .strong _ _ => Or.inl rfl

/-- Construct a structured universe relation from exactly its branch-local assumptions. -/
def universeStructuredRelation (source target : Annotation) :
    UniverseRelationAssumptions.{u} source target →
      StructuredRelation.{u + 1, u + 1, u + 1} target (Type u) (Type u)
  | .weak targetWeak => universeStructuredRelationOfWeak source target targetWeak
  | .strong _ univalent => universeStructuredRelationOfTop univalent target

/-- The admissible universe witness projects to the requested source-structured relation family. -/
@[simp] theorem universeStructuredRelation_rel (source target : Annotation)
    (assumptions : UniverseRelationAssumptions.{u} source target) :
    (universeStructuredRelation source target assumptions).rel =
      (fun A B : Type u => StructuredRelation.{u, u, u} source A B) := by
  cases assumptions with
  | weak targetWeak => rfl
  | strong targetNotWeak univalent => rfl

example (source target : Annotation) (h : target.IsUniverseWeak) :
    StructuredRelation.{u + 1, u + 1, u + 1} target (Type u) (Type u) :=
  universeStructuredRelationOfWeak source target h

example (source target : Annotation) (h : target.IsUniverseWeak) :
    (universeStructuredRelationOfWeak source target h).rel =
      (fun A B : Type u => StructuredRelation.{u, u, u} source A B) :=
  rfl

example (source : Annotation) :
    StructuredRelation.{u + 1, u + 1, u + 1} ⟨.twoA, .one⟩ (Type u) (Type u) :=
  universeStructuredRelationOfWeak source ⟨.twoA, .one⟩ ⟨trivial, trivial⟩

example (univalent : IsUnivalentUniverse.{u}) :
    IsUmap
      (fun A B : Type u =>
        StructuredRelation.{u, u, u} Annotation.equivalence A B) :=
  universeStructuredRelationTopForwardIsUmap univalent

example (univalent : IsUnivalentUniverse.{u}) :
    IsUmap
      (Converse (fun A B : Type u =>
        StructuredRelation.{u, u, u} Annotation.equivalence A B)) :=
  universeStructuredRelationTopBackwardIsUmap univalent

example (univalent : IsUnivalentUniverse.{u}) (target : Annotation) :
    StructuredRelation.{u + 1, u + 1, u + 1} target (Type u) (Type u) :=
  universeStructuredRelationOfTop univalent target

example (source target : Annotation) (targetWeak : target.IsUniverseWeak) :
    (universeStructuredRelation source target (.weak targetWeak)).rel =
      (fun A B : Type u => StructuredRelation.{u, u, u} source A B) :=
  rfl

example (univalent : IsUnivalentUniverse.{u}) (target : Annotation)
    (targetNotWeak : ¬ target.IsUniverseWeak) :
    (universeStructuredRelation Annotation.equivalence target
      (.strong targetNotWeak univalent)).rel =
        (fun A B : Type u =>
          StructuredRelation.{u, u, u} Annotation.equivalence A B) :=
  rfl

end DeepWiki.Refine
