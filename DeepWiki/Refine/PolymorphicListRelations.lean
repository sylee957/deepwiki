import DeepWiki.Refine.Dependent
import DeepWiki.Refine.RelationEquivalence
import DeepWiki.Refine.UnivalentRelationStructure

/-! # Proof-relevant relations on polymorphic lists

The pointwise list lifting preserves every one-direction map class. In particular, it lifts both
fully coherent element relations and the asymmetric `(2a, 4)` structure needed when only the
backward element relation is fully coherent. -/

namespace DeepWiki.Refine

universe u v w

namespace ListRel

/-- Mapping the function represented by a level-`2a` relation produces a related list. -/
def ofMap {A : Type u} {B : Type v} {R : A → B → Type w}
    (data : MapClass2a R) : (as : List A) → ListRel R as (as.map data.map)
  | [] => .nil
  | a :: as => .cons (data.graphToRel a (data.map a) rfl) (ofMap data as)

/-- Equality with the pointwise represented map implies the lifted list relation. -/
def graphToRel {A : Type u} {B : Type v} {R : A → B → Type w}
    (data : MapClass2a R) (as : List A) (bs : List B)
    (equality : as.map data.map = bs) : ListRel R as bs :=
  Eq.ndrec (ofMap data as) equality

/-- The lifted relation determines equality with the pointwise represented map. -/
def relToGraph {A : Type u} {B : Type v} {R : A → B → Type w}
    (data : MapClass2b R) :
    {as : List A} → {bs : List B} → ListRel R as bs → as.map data.map = bs
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons head tail =>
      congrArg₂ List.cons (data.relToGraph _ _ head) (relToGraph data tail)

/-- Reversing a list-relation witness reverses its element relation. -/
def flip {A : Type u} {B : Type v} {R : A → B → Type w} :
    {as : List A} → {bs : List B} → ListRel R as bs → ListRel (Converse R) bs as
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons head tail => .cons head (flip tail)

/-- Reverse a witness of the converse list lift back to the original relation. -/
def unflip {A : Type u} {B : Type v} {R : A → B → Type w} :
    {bs : List B} → {as : List A} → ListRel (Converse R) bs as → ListRel R as bs
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons head tail => .cons head (unflip tail)

/-- Reversing and then un-reversing a list-relation witness recovers it. -/
theorem unflip_flip {A : Type u} {B : Type v} {R : A → B → Type w}
    {as : List A} {bs : List B} (related : ListRel R as bs) :
    unflip (flip related) = related := by
  induction related with
  | nil => rfl
  | cons head tail ih =>
      exact congrArg (ListRel.cons head) ih

/-- Un-reversing and then reversing a converse-list witness recovers it. -/
theorem flip_unflip {A : Type u} {B : Type v} {R : A → B → Type w}
    {bs : List B} {as : List A} (related : ListRel (Converse R) bs as) :
    flip (unflip related) = related := by
  induction related with
  | nil => rfl
  | cons head tail ih =>
      exact congrArg (ListRel.cons head) ih

/-- The converse list relation is pointwise equivalent to the list lift of the converse relation. -/
def converseEquiv {A : Type u} {B : Type v} (R : A → B → Type w)
    (bs : List B) (as : List A) :
    Converse (ListRel R) bs as ≃ ListRel (Converse R) bs as where
  toFun := flip
  invFun := unflip
  left_inv := unflip_flip
  right_inv := flip_unflip

/-- Pointwise subsingleton element relations induce subsingleton list-relation fibers. -/
theorem witnessSubsingleton {A : Type u} {B : Type v} {R : A → B → Type w}
    (elements : ∀ a b, Subsingleton (R a b)) (as : List A) (bs : List B) :
    Subsingleton (ListRel R as bs) := by
  constructor
  intro left right
  induction left with
  | nil =>
      cases right
      rfl
  | cons head tail ih =>
      cases right with
      | cons otherHead otherTail =>
          have headEquality : head = otherHead := (elements _ _).elim _ _
          cases headEquality
          have tailEquality : tail = otherTail := ih otherTail
          cases tailEquality
          rfl

/-- A bare element relation induces a bare relation on lists. -/
def mapClass0 {A : Type u} {B : Type v} {R : A → B → Type w}
    (_data : MapClass0 R) : MapClass0 (ListRel R) :=
  ()

/-- An element map induces pointwise mapping on lists. -/
def mapClass1 {A : Type u} {B : Type v} {R : A → B → Type w}
    (data : MapClass1 R) : MapClass1 (ListRel R) where
  map := List.map data.map

/-- Element level `2a` induces list level `2a` by pointwise mapping. -/
def mapClass2a {A : Type u} {B : Type v} {R : A → B → Type w}
    (data : MapClass2a R) : MapClass2a (ListRel R) where
  map := List.map data.map
  graphToRel := graphToRel data

/-- Element level `2b` induces list level `2b` by pointwise mapping. -/
def mapClass2b {A : Type u} {B : Type v} {R : A → B → Type w}
    (data : MapClass2b R) : MapClass2b (ListRel R) where
  map := List.map data.map
  relToGraph := fun _ _ related => relToGraph data related

/-- Element level `3` induces list level `3` by pointwise mapping. -/
def mapClass3 {A : Type u} {B : Type v} {R : A → B → Type w}
    (data : MapClass3 R) : MapClass3 (ListRel R) where
  map := List.map data.map
  graphToRel := (mapClass2a data.toMapClass2a).graphToRel
  relToGraph := (mapClass2b data.toMapClass2b).relToGraph

/-- Element level `4` induces coherent list level `4` by pointwise mapping. -/
def mapClass4 {A : Type u} {B : Type v} {R : A → B → Type w}
    (data : MapClass4 R) : MapClass4 (ListRel R) where
  map := List.map data.map
  graphToRel := (mapClass2a data.toMapClass3.toMapClass2a).graphToRel
  relToGraph := (mapClass2b data.toMapClass3.toMapClass2b).relToGraph
  coherent as bs _related :=
    (witnessSubsingleton (fun a b => data.relationSubsingleton a b) as bs).elim _ _

end ListRel

/-- Lift a fully coherent relation class pointwise from elements to lists. -/
def RelationClass.listTop {A : Type u} {B : Type v} {R : A → B → Type w}
    (data : RelationClass Annotation.equivalence R) :
    RelationClass Annotation.equivalence (ListRel R) := by
  rcases data with ⟨forward, backward⟩
  cases forward with
  | four forward =>
      cases backward with
      | four backward =>
          exact ⟨.four (ListRel.mapClass4 forward),
            .four (MapClass4.congr
              (fun bs as => (ListRel.converseEquiv R bs as).symm)
              (ListRel.mapClass4 backward))⟩

/-- Lift an asymmetric `(2a, 4)` relation class pointwise from elements to lists. -/
def RelationClass.listTwoAFour {A : Type u} {B : Type v} {R : A → B → Type w}
    (data : RelationClass ⟨.twoA, .four⟩ R) :
    RelationClass ⟨.twoA, .four⟩ (ListRel R) := by
  rcases data with ⟨forward, backward⟩
  cases forward with
  | twoA forward =>
      cases backward with
      | four backward =>
          exact ⟨.twoA (ListRel.mapClass2a forward),
            .four (MapClass4.congr
              (fun bs as => (ListRel.converseEquiv R bs as).symm)
              (ListRel.mapClass4 backward))⟩

/-- Lift a top-annotated structured element relation pointwise to lists. -/
def StructuredRelation.listTop {A : Type u} {B : Type v}
    (elements : StructuredRelation.{u, v, w} Annotation.equivalence A B) :
    StructuredRelation.{u, v, max u v w} Annotation.equivalence (List A) (List B) :=
  ⟨ListRel elements.rel, RelationClass.listTop elements.relationClass⟩

/-- The top-annotated list lift exposes the pointwise list relation. -/
@[simp] theorem StructuredRelation.listTop_rel {A : Type u} {B : Type v}
    (elements : StructuredRelation.{u, v, w} Annotation.equivalence A B) :
    elements.listTop.rel = ListRel elements.rel :=
  rfl

/-- Lift a `(2a, 4)` structured element relation pointwise to lists. -/
def StructuredRelation.listTwoAFour {A : Type u} {B : Type v}
    (elements : StructuredRelation.{u, v, w} ⟨.twoA, .four⟩ A B) :
    StructuredRelation.{u, v, max u v w} ⟨.twoA, .four⟩ (List A) (List B) :=
  ⟨ListRel elements.rel, RelationClass.listTwoAFour elements.relationClass⟩

/-- The `(2a, 4)` list lift exposes the pointwise list relation. -/
@[simp] theorem StructuredRelation.listTwoAFour_rel {A : Type u} {B : Type v}
    (elements : StructuredRelation.{u, v, w} ⟨.twoA, .four⟩ A B) :
    elements.listTwoAFour.rel = ListRel elements.rel :=
  rfl

/-- The `(2a, 4)` annotation cannot be strengthened to `(4, 4)` by relation weakening. -/
theorem not_equivalence_le_twoAFour :
    ¬ Annotation.equivalence ≤ (⟨.twoA, .four⟩ : Annotation) := by
  intro comparison
  exact (show ¬ MapLevel.four ≤ MapLevel.twoA by decide) comparison.1

/-- Decidable weakening rejects a `(4, 4)` request when only `(2a, 4)` data is available. -/
@[simp] theorem cannotWeaken_twoAFour_to_equivalence :
    Annotation.canWeaken ⟨.twoA, .four⟩ Annotation.equivalence = false := by
  simp [Annotation.canWeaken, not_equivalence_le_twoAFour]

example {A : Type u} {B : Type v} {R : A → B → Type w}
    (data : MapClass4 R) : MapClass4 (ListRel R) :=
  ListRel.mapClass4 data

example {A : Type u} {B : Type v} {R : A → B → Type w}
    (data : MapClass2a R) : MapClass2a (ListRel R) :=
  ListRel.mapClass2a data

example {A : Type u} {B : Type v}
    (elements : StructuredRelation.{u, v, w} Annotation.equivalence A B) :
    StructuredRelation.{u, v, max u v w} Annotation.equivalence (List A) (List B) :=
  elements.listTop

example {A : Type u} {B : Type v}
    (elements : StructuredRelation.{u, v, w} Annotation.equivalence A B) :
    elements.listTop.rel = ListRel elements.rel :=
  rfl

example {A : Type u} {B : Type v}
    (elements : StructuredRelation.{u, v, w} ⟨.twoA, .four⟩ A B) :
    StructuredRelation.{u, v, max u v w} ⟨.twoA, .four⟩ (List A) (List B) :=
  elements.listTwoAFour

example {A : Type u} {B : Type v}
    (elements : StructuredRelation.{u, v, w} ⟨.twoA, .four⟩ A B) :
    elements.listTwoAFour.rel = ListRel elements.rel :=
  rfl

example : ¬ Annotation.equivalence ≤ (⟨.twoA, .four⟩ : Annotation) :=
  not_equivalence_le_twoAFour

example : Annotation.canWeaken ⟨.twoA, .four⟩ Annotation.equivalence = false :=
  cannotWeaken_twoAFour_to_equivalence

end DeepWiki.Refine
