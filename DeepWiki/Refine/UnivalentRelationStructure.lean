import DeepWiki.Refine.FunctionalRelation
import DeepWiki.Refine.ParametricityTranslations

/-! # Univalent universe packages as top structured relations

The relation package used by the univalent parametricity translation is equivalent, without a
global univalence axiom, to the `(4, 4)` endpoint of the annotation-indexed relation hierarchy.
-/

namespace DeepWiki.Refine

universe u v w

/-- A univalent universe package coherently represents its carried equivalence forward. -/
def UnivalentRelation.forwardIsUmap {A B : Type u} (package : UnivalentRelation A B) :
    IsUmap package.relation where
  map := package.equivalence
  graphToRel a b path :=
    (package.relationEquiv a b).symm
      ⟨⟨(package.equivalence.symm_apply_apply a).symm.trans
        (congrArg package.equivalence.symm path)⟩⟩
  relToGraph a b related :=
    congrArg package.equivalence (package.relationEquiv a b related).down.down |>.trans
      (package.equivalence.apply_symm_apply b)
  coherent a b related := by
    apply (package.relationEquiv a b).injective
    exact Subsingleton.elim _ _

/-- A univalent universe package coherently represents its carried equivalence backward. -/
def UnivalentRelation.backwardIsUmap {A B : Type u} (package : UnivalentRelation A B) :
    IsUmap (Converse package.relation) where
  map := package.equivalence.symm
  graphToRel b a path :=
    (package.relationEquiv a b).symm ⟨⟨path.symm⟩⟩
  relToGraph b a related :=
    (package.relationEquiv a b related).down.down.symm
  coherent b a related := by
    apply (package.relationEquiv a b).injective
    exact Subsingleton.elim _ _

/-- A univalent universe package gives a relation at the top `(4, 4)` annotation. -/
def UnivalentRelation.toStructuredRelationTop {A B : Type u}
    (package : UnivalentRelation A B) :
    StructuredRelation.{u, u, u} Annotation.equivalence A B :=
  ⟨package.relation, .four package.forwardIsUmap, .four package.backwardIsUmap⟩

/-- A top structured relation determines a univalent universe package. -/
def StructuredRelation.toUnivalentRelation {A B : Type u}
    (relation : StructuredRelation.{u, u, u} Annotation.equivalence A B) :
    UnivalentRelation A B := by
  rcases relation with ⟨R, relationClass⟩
  cases relationClass.1 with
  | four forward =>
    cases relationClass.2 with
    | four backward =>
      let equivalence : A ≃ B := BiMapClass3.toEquiv
        { forward := MapClass4.toMapClass3 forward
          backward := MapClass4.toMapClass3 backward }
      refine
        { equivalence := equivalence
          relation := R
          relationEquiv := ?_ }
      intro a b
      change R a b ≃ ULift.{u} (PLift (a = backward.map b))
      exact
        { toFun := fun related => ⟨⟨(backward.relToGraph b a related).symm⟩⟩
          invFun := fun path => backward.graphToRel b a path.down.down.symm
          left_inv := backward.coherent b a
          right_inv := fun _ => Subsingleton.elim _ _ }

/-- Level-`4` coherence makes every fiber of the represented relation a subsingleton. -/
theorem MapClass4.relationSubsingleton {A : Type u} {B : Type v} {R : A → B → Type w}
    (data : MapClass4 R) (a : A) (b : B) : Subsingleton (R a b) := by
  constructor
  intro left right
  calc
    left = data.graphToRel a b (data.relToGraph a b left) :=
      (data.coherent a b left).symm
    _ = data.graphToRel a b (data.relToGraph a b right) := by
      congr 1
    _ = right := data.coherent a b right

/-- Level-`4` structure on a fixed relation is unique. -/
theorem mapClass4_subsingleton {A : Type u} {B : Type v} (R : A → B → Type w) :
    Subsingleton (MapClass4 R) := by
  constructor
  intro left right
  calc
    left = IsFun.toIsUmap (IsUmap.toIsFun left) :=
      (IsUmap.toIsFun_toIsUmap left).symm
    _ = IsFun.toIsUmap (IsUmap.toIsFun right) := congrArg IsFun.toIsUmap
      ((isFun_subsingleton R).elim (IsUmap.toIsFun left) (IsUmap.toIsFun right))
    _ = right := IsUmap.toIsFun_toIsUmap right

/-- The top relation class carried by a fixed relation is unique. -/
theorem equivalenceRelationClass_subsingleton {A : Type u} {B : Type v}
    (R : A → B → Type w) :
    Subsingleton (RelationClass Annotation.equivalence R) := by
  constructor
  rintro ⟨leftForward, leftBackward⟩ ⟨rightForward, rightBackward⟩
  cases leftForward with
  | four leftForward =>
    cases leftBackward with
    | four leftBackward =>
      cases rightForward with
      | four rightForward =>
        cases rightBackward with
        | four rightBackward =>
          congr
          · exact (mapClass4_subsingleton R).elim _ _
          · exact (mapClass4_subsingleton (Converse R)).elim _ _

/-- Conversion from a univalent universe package to a top structured relation is left-invertible. -/
@[simp] theorem UnivalentRelation.toStructuredRelationTop_toUnivalentRelation
    {A B : Type u} (package : UnivalentRelation A B) :
    package.toStructuredRelationTop.toUnivalentRelation = package := by
  rcases package with ⟨equivalence, relation, relationEquiv⟩
  apply UnivalentRelation.ext
  · apply Equiv.ext
    intro a
    rfl
  · rfl

/-- Conversion from a top structured relation to a univalent universe package is left-invertible. -/
@[simp] theorem StructuredRelation.toUnivalentRelation_toStructuredRelationTop
    {A B : Type u}
    (relation : StructuredRelation.{u, u, u} Annotation.equivalence A B) :
    relation.toUnivalentRelation.toStructuredRelationTop = relation := by
  rcases relation with ⟨R, forwardClass, backwardClass⟩
  cases forwardClass with
  | four forward =>
    cases backwardClass with
    | four backward =>
      apply Sigma.ext
        (x := UnivalentRelation.toStructuredRelationTop
          (StructuredRelation.toUnivalentRelation
            (⟨R, .four forward, .four backward⟩ :
              StructuredRelation.{u, u, u} Annotation.equivalence A B)))
        (y := (⟨R, .four forward, .four backward⟩ :
          StructuredRelation.{u, u, u} Annotation.equivalence A B)) rfl
      exact heq_of_eq ((equivalenceRelationClass_subsingleton R).elim _ _)

/-- Univalent universe packages and top structured relations are equivalent without ambient univalence. -/
def univalentRelationEquivStructuredRelationTop (A B : Type u) :
    UnivalentRelation A B ≃
      StructuredRelation.{u, u, u} Annotation.equivalence A B where
  toFun := UnivalentRelation.toStructuredRelationTop
  invFun := StructuredRelation.toUnivalentRelation
  left_inv := UnivalentRelation.toStructuredRelationTop_toUnivalentRelation
  right_inv := StructuredRelation.toUnivalentRelation_toStructuredRelationTop

example {A B : Type u} (package : UnivalentRelation A B) :
    StructuredRelation.{u, u, u} Annotation.equivalence A B :=
  package.toStructuredRelationTop

example {A B : Type u}
    (relation : StructuredRelation.{u, u, u} Annotation.equivalence A B) :
    UnivalentRelation A B :=
  relation.toUnivalentRelation

example (A B : Type u) :
    UnivalentRelation A B ≃
      StructuredRelation.{u, u, u} Annotation.equivalence A B :=
  univalentRelationEquivStructuredRelationTop A B

example {A : Type u} {B : Type v} {R : A → B → Type w}
    (data : MapClass4 R) (a : A) (b : B) : Subsingleton (R a b) :=
  data.relationSubsingleton a b

example {A : Type u} {B : Type v} (R : A → B → Type w) :
    Subsingleton (MapClass4 R) :=
  mapClass4_subsingleton R

example {A : Type u} {B : Type v} (R : A → B → Type w) :
    Subsingleton (RelationClass Annotation.equivalence R) :=
  equivalenceRelationClass_subsingleton R

end DeepWiki.Refine
