import DeepWiki.Refine.DependencyRequirements
import DeepWiki.Refine.RelationEquivalence

/-! # Structured respectful-arrow relations

The non-dependent respectful arrow inherits directional map data contravariantly from its domain
relation and covariantly from its codomain relation. -/

namespace DeepWiki.Refine

universe u v u' v' w w'

/-- The proof-relevant respectful arrow between two heterogeneous relations. -/
def ArrowRelation {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    (R : A → B → Sort w) (S : C → D → Sort w')
    (f : A → C) (g : B → D) :=
  ∀ a b, R a b → S (f a) (g b)

/-- On proposition-valued relations, `ArrowRelation` is the ordinary `Respectful` arrow. -/
theorem arrowRelation_iff_respectful {A : Type u} {B : Type v}
    {C : Type u'} {D : Type v'} (R : A → B → Prop) (S : C → D → Prop)
    (f : A → C) (g : B → D) :
    ArrowRelation R S f g ↔ Respectful R S f g :=
  Iff.rfl

namespace ArrowRelation

/-- Bare domain and codomain relations induce a bare respectful-arrow relation. -/
def mapClass0 {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (_domain : MapClass0 R) (_codomain : MapClass0 S) :
    MapClass0 (ArrowRelation R S) :=
  ()

/-- A backward domain map and a forward codomain map induce a forward function map. -/
def mapClass1 {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (domain : MapClass1 (Converse R)) (codomain : MapClass1 S) :
    MapClass1 (ArrowRelation R S) where
  map f b := codomain.map (f (domain.map b))

/-- Domain level `2b` in reverse and codomain level `2a` induce arrow level `2a`. -/
def mapClass2a {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (domain : MapClass2b (Converse R)) (codomain : MapClass2a S) :
    MapClass2a (ArrowRelation R S) where
  map f b := codomain.map (f (domain.map b))
  graphToRel f g hfg a b rab :=
    codomain.graphToRel (f a) (g b) <|
      (congrArg codomain.map (congrArg f (domain.relToGraph b a rab))).symm.trans
        (congrFun hfg b)

/-- Domain level `2a` in reverse and codomain level `2b` induce arrow level `2b`. -/
def mapClass2b {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (domain : MapClass2a (Converse R)) (codomain : MapClass2b S) :
    MapClass2b (ArrowRelation R S) where
  map f b := codomain.map (f (domain.map b))
  relToGraph f g hfg := by
    funext b
    exact codomain.relToGraph (f (domain.map b)) (g b)
      (hfg (domain.map b) b (domain.graphToRel b (domain.map b) rfl))

/-- Reversed domain and forward codomain level `3` data induce arrow level `3`. -/
def mapClass3 {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (domain : MapClass3 (Converse R)) (codomain : MapClass3 S) :
    MapClass3 (ArrowRelation R S) where
  map f b := codomain.map (f (domain.map b))
  graphToRel := (mapClass2a domain.toMapClass2b codomain.toMapClass2a).graphToRel
  relToGraph := (mapClass2b domain.toMapClass2a codomain.toMapClass2b).relToGraph

/-- In proof-irrelevant Lean, domain level `3` and codomain level `4` induce arrow level `4`. -/
def mapClass4OfDomain3 {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (domain : MapClass3 (Converse R)) (codomain : MapClass4 S) :
    MapClass4 (ArrowRelation R S) where
  map f b := codomain.map (f (domain.map b))
  graphToRel := (mapClass2a domain.toMapClass2b
    codomain.toMapClass3.toMapClass2a).graphToRel
  relToGraph := (mapClass2b domain.toMapClass2a
    codomain.toMapClass3.toMapClass2b).relToGraph
  coherent f g hfg := by
    funext a b rab
    simp only [mapClass2a]
    exact
      (congrArg (codomain.graphToRel (f a) (g b))
        (Subsingleton.elim _ (codomain.relToGraph (f a) (g b) (hfg a b rab)))).trans
      (codomain.coherent (f a) (g b) (hfg a b rab))

/-- Reversed domain and forward codomain level `4` data induce coherent arrow level `4`. -/
def mapClass4 {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (domain : MapClass4 (Converse R)) (codomain : MapClass4 S) :
    MapClass4 (ArrowRelation R S) :=
  mapClass4OfDomain3 domain.toMapClass3 codomain

/-- Reversing a respectful arrow is pointwise equivalent to reversing both input relations. -/
def converseEquiv {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    (R : A → B → Sort w) (S : C → D → Sort w') (g : B → D) (f : A → C) :
    Converse (ArrowRelation R S) g f ≃
      ArrowRelation (Converse R) (Converse S) g f where
  toFun h b a rab := h a b rab
  invFun h a b rab := h b a rab
  left_inv _ := rfl
  right_inv _ := rfl

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (hR : MapClass0 R) (hS : MapClass0 S) : MapClass0 (ArrowRelation R S) :=
  mapClass0 hR hS

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (hR : MapClass1 (Converse R)) (hS : MapClass1 S) : MapClass1 (ArrowRelation R S) :=
  mapClass1 hR hS

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (hR : MapClass2b (Converse R)) (hS : MapClass2a S) : MapClass2a (ArrowRelation R S) :=
  mapClass2a hR hS

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (hR : MapClass2a (Converse R)) (hS : MapClass2b S) : MapClass2b (ArrowRelation R S) :=
  mapClass2b hR hS

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (hR : MapClass3 (Converse R)) (hS : MapClass3 S) : MapClass3 (ArrowRelation R S) :=
  mapClass3 hR hS

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (hR : MapClass4 (Converse R)) (hS : MapClass4 S) : MapClass4 (ArrowRelation R S) :=
  mapClass4 hR hS

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'}
    (hR : MapClass3 (Converse R)) (hS : MapClass4 S) : MapClass4 (ArrowRelation R S) :=
  mapClass4OfDomain3 hR hS

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    (R : A → B → Sort w) (S : C → D → Sort w') (g : B → D) (f : A → C) :
    Converse (ArrowRelation R S) g f ≃
      ArrowRelation (Converse R) (Converse S) g f :=
  converseEquiv R S g f

end ArrowRelation

/-- Indexed arrow construction implements the one-sided arrow dependency table. -/
def MapClass.arrow {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'} {level : MapLevel}
    (domain : MapClass (Converse R) level.arrowDomainRequirement)
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
      | four domain =>
          cases codomain with
          | four codomain => exact .four (ArrowRelation.mapClass4 domain codomain)

/-- Bidirectional arrow structure uses exactly the reconstructed domain and codomain requirements. -/
def RelationClass.arrow {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'} (γ : Annotation)
    (domain : RelationClass (arrowRequirements γ).1 R)
    (codomain : RelationClass γ S) : RelationClass γ (ArrowRelation R S) :=
  ⟨MapClass.arrow domain.2 codomain.1,
    MapClass.congr (fun g f => (ArrowRelation.converseEquiv R S g f).symm)
      (MapClass.arrow domain.1 codomain.2)⟩

/-- Construct a structured respectful-arrow relation from structured domain and codomain relations. -/
def StructuredRelation.arrow {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    (gamma : Annotation)
    (domain : StructuredRelation (arrowRequirements gamma).1 A B)
    (codomain : StructuredRelation gamma C D) :
    StructuredRelation gamma (A → C) (B → D) :=
  ⟨ArrowRelation domain.rel codomain.rel,
    RelationClass.arrow gamma domain.relationClass codomain.relationClass⟩

/-- The relation underlying `StructuredRelation.arrow` is the respectful-arrow relation. -/
@[simp] theorem StructuredRelation.arrow_rel {A : Type u} {B : Type v}
    {C : Type u'} {D : Type v'} (gamma : Annotation)
    (domain : StructuredRelation (arrowRequirements gamma).1 A B)
    (codomain : StructuredRelation gamma C D) :
    (StructuredRelation.arrow gamma domain codomain).rel =
      ArrowRelation domain.rel codomain.rel :=
  rfl

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'} {level : MapLevel}
    (domain : MapClass (Converse R) level.arrowDomainRequirement)
    (codomain : MapClass S level) : MapClass (ArrowRelation R S) level :=
  MapClass.arrow domain codomain

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Sort w} {S : C → D → Sort w'} (γ : Annotation)
    (domain : RelationClass (arrowRequirements γ).1 R)
    (codomain : RelationClass γ S) : RelationClass γ (ArrowRelation R S) :=
  RelationClass.arrow γ domain codomain

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'} (γ : Annotation)
    (domain : StructuredRelation (arrowRequirements γ).1 A B)
    (codomain : StructuredRelation γ C D) :
    StructuredRelation γ (A → C) (B → D) :=
  StructuredRelation.arrow γ domain codomain

example {A : Type u} {B : Type v} {C : Type u'} {D : Type v'} (γ : Annotation)
    (domain : StructuredRelation (arrowRequirements γ).1 A B)
    (codomain : StructuredRelation γ C D) :
    (StructuredRelation.arrow γ domain codomain).rel =
      ArrowRelation domain.rel codomain.rel :=
  rfl

end DeepWiki.Refine
