import DeepWiki.Refine.Dependent
import DeepWiki.Refine.DependencyRequirements
import DeepWiki.Refine.RelationEquivalence
import DeepWiki.Refine.RelationStructure

/-! # Structured dependent-product relations

The dependent respectful product inherits one-direction map data contravariantly from its domain
relation and covariantly from every related fiber relation. -/

namespace DeepWiki.Refine

universe u v u' v' w w'

namespace DependentRespectful

/-- Bare domain and fiber relations induce a bare dependent-product relation. -/
def mapClass0 {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    (_domain : MapClass0 R) (_fibers : ∀ a b (r : R a b), MapClass0 (S a b r)) :
    MapClass0 (DependentRespectful R S) :=
  ()

/-- A backward graph-producing domain map and forward fiber maps induce a function map. -/
def mapClass1 {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    (domain : MapClass2a (Converse R))
    (fibers : ∀ a b (r : R a b), MapClass1 (S a b r)) :
    MapClass1 (DependentRespectful R S) where
  map f b :=
    let r := domain.graphToRel b (domain.map b) rfl
    (fibers (domain.map b) b r).map (f (domain.map b))

/-- Coherent backward domain data and graph-producing fibers induce product level `2a`. -/
def mapClass2a {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    (domain : MapClass4 (Converse R))
    (fibers : ∀ a b (r : R a b), MapClass2a (S a b r)) :
    MapClass2a (DependentRespectful R S) where
  map := (mapClass1 domain.toMapClass3.toMapClass2a
    (fun a b r => (fibers a b r).toMapClass1)).map
  graphToRel f g hfg a b r := by
    let p : domain.map b = a := domain.relToGraph b a r
    cases p
    have hr : domain.graphToRel b (domain.map b) rfl = r := by
      calc
        domain.graphToRel b (domain.map b) rfl =
            domain.graphToRel b (domain.map b)
              (domain.relToGraph b (domain.map b) r) := by
                congr 1
        _ = r := domain.coherent b (domain.map b) r
    cases hr
    exact (fibers (domain.map b) b
      (domain.graphToRel b (domain.map b) rfl)).graphToRel _ _ (congrFun hfg b)

/-- A backward graph-producing domain map and graph-determined fibers induce product level `2b`. -/
def mapClass2b {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    (domain : MapClass2a (Converse R))
    (fibers : ∀ a b (r : R a b), MapClass2b (S a b r)) :
    MapClass2b (DependentRespectful R S) where
  map := (mapClass1 domain (fun a b r => (fibers a b r).toMapClass1)).map
  relToGraph f g hfg := by
    funext b
    let r := domain.graphToRel b (domain.map b) rfl
    exact (fibers (domain.map b) b r).relToGraph _ _
      (hfg (domain.map b) b r)

/-- Coherent backward domain data and bidirectional fibers induce product level `3`. -/
def mapClass3 {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    (domain : MapClass4 (Converse R))
    (fibers : ∀ a b (r : R a b), MapClass3 (S a b r)) :
    MapClass3 (DependentRespectful R S) where
  map := (mapClass1 domain.toMapClass3.toMapClass2a
    (fun a b r => (fibers a b r).toMapClass2a.toMapClass1)).map
  graphToRel := (mapClass2a domain (fun a b r => (fibers a b r).toMapClass2a)).graphToRel
  relToGraph := (mapClass2b domain.toMapClass3.toMapClass2a
    (fun a b r => (fibers a b r).toMapClass2b)).relToGraph

/-- Fully coherent backward domain and fiber data induce coherent product level `4`. -/
def mapClass4 {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    (domain : MapClass4 (Converse R))
    (fibers : ∀ a b (r : R a b), MapClass4 (S a b r)) :
    MapClass4 (DependentRespectful R S) where
  map := (mapClass1 domain.toMapClass3.toMapClass2a
    (fun a b r => (fibers a b r).toMapClass3.toMapClass2a.toMapClass1)).map
  graphToRel := (mapClass2a domain
    (fun a b r => (fibers a b r).toMapClass3.toMapClass2a)).graphToRel
  relToGraph := (mapClass2b domain.toMapClass3.toMapClass2a
    (fun a b r => (fibers a b r).toMapClass3.toMapClass2b)).relToGraph
  coherent f g hfg := by
    funext a b r
    let p : domain.map b = a := domain.relToGraph b a r
    cases p
    have hr : domain.graphToRel b (domain.map b) rfl = r := by
      calc
        domain.graphToRel b (domain.map b) rfl =
            domain.graphToRel b (domain.map b)
              (domain.relToGraph b (domain.map b) r) := by
                congr 1
        _ = r := domain.coherent b (domain.map b) r
    cases hr
    exact (fibers (domain.map b) b
      (domain.graphToRel b (domain.map b) rfl)).coherent _ _ _

example {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    (hR : MapClass0 R) (hS : ∀ a b (r : R a b), MapClass0 (S a b r)) :
    MapClass0 (DependentRespectful R S) :=
  mapClass0 hR hS

example {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    (hR : MapClass2a (Converse R))
    (hS : ∀ a b (r : R a b), MapClass1 (S a b r)) :
    MapClass1 (DependentRespectful R S) :=
  mapClass1 hR hS

example {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    (hR : MapClass4 (Converse R))
    (hS : ∀ a b (r : R a b), MapClass2a (S a b r)) :
    MapClass2a (DependentRespectful R S) :=
  mapClass2a hR hS

example {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    (hR : MapClass2a (Converse R))
    (hS : ∀ a b (r : R a b), MapClass2b (S a b r)) :
    MapClass2b (DependentRespectful R S) :=
  mapClass2b hR hS

example {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    (hR : MapClass4 (Converse R))
    (hS : ∀ a b (r : R a b), MapClass3 (S a b r)) :
    MapClass3 (DependentRespectful R S) :=
  mapClass3 hR hS

example {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    (hR : MapClass4 (Converse R))
    (hS : ∀ a b (r : R a b), MapClass4 (S a b r)) :
    MapClass4 (DependentRespectful R S) :=
  mapClass4 hR hS

end DependentRespectful

/-- Build indexed one-direction map data from the dependent-product dependency table. -/
def MapClass.pi {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'} {level : MapLevel}
    (domain : MapClass (Converse R) level.piDomainRequirement)
    (fibers : ∀ a b (r : R a b), MapClass (S a b r) level) :
    MapClass (DependentRespectful R S) level := by
  cases level with
  | zero => exact .zero
  | one =>
      cases domain with
      | twoA domain =>
          exact .one (DependentRespectful.mapClass1 domain (fun a b r => by
            cases fibers a b r with
            | one fiber => exact fiber))
  | twoA =>
      cases domain with
      | four domain =>
          exact .twoA (DependentRespectful.mapClass2a domain (fun a b r => by
            cases fibers a b r with
            | twoA fiber => exact fiber))
  | twoB =>
      cases domain with
      | twoA domain =>
          exact .twoB (DependentRespectful.mapClass2b domain (fun a b r => by
            cases fibers a b r with
            | twoB fiber => exact fiber))
  | three =>
      cases domain with
      | four domain =>
          exact .three (DependentRespectful.mapClass3 domain (fun a b r => by
            cases fibers a b r with
            | three fiber => exact fiber))
  | four =>
      cases domain with
      | four domain =>
          exact .four (DependentRespectful.mapClass4 domain (fun a b r => by
            cases fibers a b r with
            | four fiber => exact fiber))

/-- Reverse every fiber relation while exchanging its left and right indices. -/
def DependentRespectful.converseFiber {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    (S : ∀ a b, R a b → C a → D b → Sort w')
    (b : B) (a : A) (r : Converse R b a) : D b → C a → Sort w' :=
  Converse (S a b r)

/-- Reversing a dependent product is pointwise equivalent to reversing its domain and fibers. -/
def DependentRespectful.converseEquiv {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    (S : ∀ a b, R a b → C a → D b → Sort w') :
    PointwiseRelationEquiv (Converse (DependentRespectful R S))
      (DependentRespectful (Converse R) (DependentRespectful.converseFiber S)) :=
  fun _ _ =>
    { toFun := fun h b a r => h a b r
      invFun := fun h a b r => h b a r
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Construct an annotated dependent product from its computed domain requirement and fibers. -/
def RelationClass.pi {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'} (γ : Annotation)
    (domain : RelationClass (dependentProductRequirements γ).1 R)
    (fibers : ∀ a b (r : R a b), RelationClass γ (S a b r)) :
    RelationClass γ (DependentRespectful R S) := by
  refine ⟨?_, ?_⟩
  · exact MapClass.pi domain.2 (fun a b r => (fibers a b r).1)
  · apply MapClass.congr
      (fun g f => (DependentRespectful.converseEquiv S g f).symm)
    exact MapClass.pi domain.1 (fun b a r => (fibers a b r).2)

/-- Construct a structured dependent-product relation from structured domain and fiber relations. -/
def StructuredRelation.pi {A : Type u} {B : Type v}
    {C : A → Type u'} {D : B → Type v'} (gamma : Annotation)
    (domain : StructuredRelation (dependentProductRequirements gamma).1 A B)
    (fibers : ∀ a b (_r : domain.rel a b), StructuredRelation gamma (C a) (D b)) :
    StructuredRelation gamma ((a : A) → C a) ((b : B) → D b) :=
  ⟨DependentRespectful domain.rel (fun a b r => (fibers a b r).rel),
    RelationClass.pi gamma domain.relationClass
      (fun a b r => (fibers a b r).relationClass)⟩

/-- The relation underlying `StructuredRelation.pi` is the dependent respectful relation. -/
@[simp] theorem StructuredRelation.pi_rel {A : Type u} {B : Type v}
    {C : A → Type u'} {D : B → Type v'} (gamma : Annotation)
    (domain : StructuredRelation (dependentProductRequirements gamma).1 A B)
    (fibers : ∀ a b (_r : domain.rel a b), StructuredRelation gamma (C a) (D b)) :
    (StructuredRelation.pi gamma domain fibers).rel =
      DependentRespectful domain.rel (fun a b r => (fibers a b r).rel) :=
  rfl

example {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'} {level : MapLevel}
    (hR : MapClass (Converse R) level.piDomainRequirement)
    (hS : ∀ a b (r : R a b), MapClass (S a b r) level) :
    MapClass (DependentRespectful R S) level :=
  MapClass.pi hR hS

example {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    (S : ∀ a b, R a b → C a → D b → Sort w') :
    PointwiseRelationEquiv (Converse (DependentRespectful R S))
      (DependentRespectful (Converse R) (DependentRespectful.converseFiber S)) :=
  DependentRespectful.converseEquiv S

example {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    (S : ∀ a b, R a b → C a → D b → Sort w') (b : B) (a : A)
    (r : Converse R b a) :
    DependentRespectful.converseFiber S b a r = Converse (S a b r) :=
  rfl

example {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'} (γ : Annotation)
    (hR : RelationClass (dependentProductRequirements γ).1 R)
    (hS : ∀ a b (r : R a b), RelationClass γ (S a b r)) :
    RelationClass γ (DependentRespectful R S) :=
  RelationClass.pi γ hR hS

example {A : Type u} {B : Type v} {C : A → Type u'} {D : B → Type v'}
    (γ : Annotation)
    (domain : StructuredRelation (dependentProductRequirements γ).1 A B)
    (fibers : ∀ a b (_r : domain.rel a b), StructuredRelation γ (C a) (D b)) :
    StructuredRelation γ ((a : A) → C a) ((b : B) → D b) :=
  StructuredRelation.pi γ domain fibers

example {A : Type u} {B : Type v} {C : A → Type u'} {D : B → Type v'}
    (γ : Annotation)
    (domain : StructuredRelation (dependentProductRequirements γ).1 A B)
    (fibers : ∀ a b (_r : domain.rel a b), StructuredRelation γ (C a) (D b)) :
    (StructuredRelation.pi γ domain fibers).rel =
      DependentRespectful domain.rel (fun a b r => (fibers a b r).rel) :=
  rfl

end DeepWiki.Refine
