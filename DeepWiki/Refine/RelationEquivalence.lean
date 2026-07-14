import DeepWiki.Refine.RelationStructure

/-! # Equivalence of heterogeneous relations

Directional map structure transports pointwise across equivalences of relation witnesses. -/

namespace DeepWiki.Refine

universe u v w w'

/-- A pointwise equivalence between two heterogeneous relation families. -/
abbrev PointwiseRelationEquiv {A : Type u} {B : Type v}
    (R : A → B → Sort w) (S : A → B → Sort w') :=
  ∀ a b, R a b ≃ S a b

/-- Bare relation structure transports across a pointwise relation equivalence. -/
def MapClass0.congr {A : Type u} {B : Type v}
    {R : A → B → Sort w} {S : A → B → Sort w'}
    (_e : PointwiseRelationEquiv R S) (_h : MapClass0 R) : MapClass0 S :=
  ()

/-- Level-`1` map structure transports across a pointwise relation equivalence. -/
def MapClass1.congr {A : Type u} {B : Type v}
    {R : A → B → Sort w} {S : A → B → Sort w'}
    (_e : PointwiseRelationEquiv R S) (h : MapClass1 R) : MapClass1 S where
  map := h.map

/-- Level-`2a` map structure transports covariantly across relation equivalence. -/
def MapClass2a.congr {A : Type u} {B : Type v}
    {R : A → B → Sort w} {S : A → B → Sort w'}
    (e : PointwiseRelationEquiv R S) (h : MapClass2a R) : MapClass2a S where
  map := h.map
  graphToRel a b hab := e a b (h.graphToRel a b hab)

/-- Level-`2b` map structure transports contravariantly across relation equivalence. -/
def MapClass2b.congr {A : Type u} {B : Type v}
    {R : A → B → Sort w} {S : A → B → Sort w'}
    (e : PointwiseRelationEquiv R S) (h : MapClass2b R) : MapClass2b S where
  map := h.map
  relToGraph a b hab := h.relToGraph a b ((e a b).symm hab)

/-- Level-`3` map structure transports both graph laws across relation equivalence. -/
def MapClass3.congr {A : Type u} {B : Type v}
    {R : A → B → Sort w} {S : A → B → Sort w'}
    (e : PointwiseRelationEquiv R S) (h : MapClass3 R) : MapClass3 S where
  map := h.map
  graphToRel a b hab := e a b (h.graphToRel a b hab)
  relToGraph a b hab := h.relToGraph a b ((e a b).symm hab)

/-- Level-`4` coherence transports without discarding relation witnesses. -/
def MapClass4.congr {A : Type u} {B : Type v}
    {R : A → B → Sort w} {S : A → B → Sort w'}
    (e : PointwiseRelationEquiv R S) (h : MapClass4 R) : MapClass4 S where
  map := h.map
  graphToRel a b hab := e a b (h.graphToRel a b hab)
  relToGraph a b hab := h.relToGraph a b ((e a b).symm hab)
  coherent a b hab := by
    calc
      e a b (h.graphToRel a b (h.relToGraph a b ((e a b).symm hab))) =
          e a b ((e a b).symm hab) := congrArg (e a b) (h.coherent a b ((e a b).symm hab))
      _ = hab := (e a b).apply_symm_apply hab

/-- Indexed map structure transports across a pointwise relation equivalence at every level. -/
def MapClass.congr {A : Type u} {B : Type v}
    {R : A → B → Sort w} {S : A → B → Sort w'}
    (e : PointwiseRelationEquiv R S) {level : MapLevel} :
    MapClass R level → MapClass S level
  | .zero => .zero
  | .one h => .one (MapClass1.congr e h)
  | .twoA h => .twoA (MapClass2a.congr e h)
  | .twoB h => .twoB (MapClass2b.congr e h)
  | .three h => .three (MapClass3.congr e h)
  | .four h => .four (MapClass4.congr e h)

example {A : Type u} {B : Type v} {R : A → B → Sort w} {S : A → B → Sort w'}
    (e : PointwiseRelationEquiv R S) (h : MapClass0 R) : MapClass0 S :=
  MapClass0.congr e h

example {A : Type u} {B : Type v} {R : A → B → Sort w} {S : A → B → Sort w'}
    (e : PointwiseRelationEquiv R S) (h : MapClass1 R) : MapClass1 S :=
  MapClass1.congr e h

example {A : Type u} {B : Type v} {R : A → B → Sort w} {S : A → B → Sort w'}
    (e : PointwiseRelationEquiv R S) (h : MapClass2a R) : MapClass2a S :=
  MapClass2a.congr e h

example {A : Type u} {B : Type v} {R : A → B → Sort w} {S : A → B → Sort w'}
    (e : PointwiseRelationEquiv R S) (h : MapClass2b R) : MapClass2b S :=
  MapClass2b.congr e h

example {A : Type u} {B : Type v} {R : A → B → Sort w} {S : A → B → Sort w'}
    (e : PointwiseRelationEquiv R S) (h : MapClass3 R) : MapClass3 S :=
  MapClass3.congr e h

example {A : Type u} {B : Type v} {R : A → B → Sort w} {S : A → B → Sort w'}
    (e : PointwiseRelationEquiv R S) (h : MapClass4 R) : MapClass4 S :=
  MapClass4.congr e h

example {A : Type u} {B : Type v} {R : A → B → Sort w} {S : A → B → Sort w'}
    (e : PointwiseRelationEquiv R S) {level : MapLevel} (h : MapClass R level) :
    MapClass S level :=
  MapClass.congr e h

end DeepWiki.Refine
