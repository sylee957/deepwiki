import DeepWiki.Refine.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.PartialOrder

/-! # Structured heterogeneous relations

Proof-relevant one-direction map classes, their bidirectional pairing, and weakening projections.
These structures expose how much computational information a heterogeneous relation carries. -/

namespace DeepWiki.Refine

universe u v w w'

/-- `Converse R` relates `b` to `a` exactly when `R` relates `a` to `b`. -/
def Converse {A : Type u} {B : Type v} (R : A → B → Sort w) : B → A → Sort w :=
  fun b a => R a b

/-- A map's graph implies the heterogeneous relation. -/
abbrev GraphToRel {A : Type u} {B : Type v} (R : A → B → Sort w) (map : A → B) :=
  ∀ a b, map a = b → R a b

/-- The heterogeneous relation implies membership in a map's graph. -/
abbrev RelToGraph {A : Type u} {B : Type v} (R : A → B → Sort w) (map : A → B) :=
  ∀ a b, R a b → map a = b

/-- Level `0`: a bare relation carries no directional map data. -/
abbrev MapClass0 {A : Type u} {B : Type v} (_R : A → B → Sort w) := Unit

/-- Level `1`: a relation is accompanied by an otherwise unconstrained forward map. -/
structure MapClass1 {A : Type u} {B : Type v} (_R : A → B → Sort w) where
  /-- The forward map carried independently of the relation. -/
  map : A → B

/-- Level `2a`: equality with the forward map implies the relation. -/
structure MapClass2a {A : Type u} {B : Type v} (R : A → B → Sort w) where
  /-- The forward map represented by the relation. -/
  map : A → B
  /-- The map's graph is contained in the relation. -/
  graphToRel : GraphToRel R map

/-- Level `2b`: the relation implies equality with the forward map. -/
structure MapClass2b {A : Type u} {B : Type v} (R : A → B → Sort w) where
  /-- The forward map represented by the relation. -/
  map : A → B
  /-- The relation is contained in the map's graph. -/
  relToGraph : RelToGraph R map

/-- Level `3`: the relation and the graph of a forward map imply one another. -/
structure MapClass3 {A : Type u} {B : Type v} (R : A → B → Sort w) where
  /-- The forward map represented by the relation. -/
  map : A → B
  /-- The map's graph is contained in the relation. -/
  graphToRel : GraphToRel R map
  /-- The relation is contained in the map's graph. -/
  relToGraph : RelToGraph R map

/-- Level `4`: a level-`3` map whose graph-to-relation round trip preserves relation witnesses. -/
structure MapClass4 {A : Type u} {B : Type v} (R : A → B → Sort w) where
  /-- The forward map represented by the relation. -/
  map : A → B
  /-- The map's graph is contained in the relation. -/
  graphToRel : GraphToRel R map
  /-- The relation is contained in the map's graph. -/
  relToGraph : RelToGraph R map
  /-- Converting a relation witness to graph equality and back preserves the witness. -/
  coherent : ∀ a b (r : R a b), graphToRel a b (relToGraph a b r) = r

/-- The six one-direction structure levels, with `twoA` and `twoB` as distinct branches. -/
inductive MapLevel where
  | zero
  | one
  | twoA
  | twoB
  | three
  | four
  deriving DecidableEq, Repr

/-- The structure order on one-direction levels, with incomparable level-`2` variants. -/
protected def MapLevel.le : MapLevel → MapLevel → Prop
  | .zero, _ => True
  | .one, .one | .one, .twoA | .one, .twoB | .one, .three | .one, .four => True
  | .twoA, .twoA | .twoA, .three | .twoA, .four => True
  | .twoB, .twoB | .twoB, .three | .twoB, .four => True
  | .three, .three | .three, .four => True
  | .four, .four => True
  | _, _ => False

/-- `MapLevel` is ordered by the amount of directional structure carried. -/
instance : PartialOrder MapLevel where
  le := MapLevel.le
  le_refl a := by cases a <;> trivial
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp_all [MapLevel.le]
  le_antisymm a b hab hba := by
    cases a <;> cases b <;> simp_all [MapLevel.le]

/-- Decision procedure for comparison in the finite map-level lattice. -/
protected def MapLevel.decLe : (a b : MapLevel) → Decidable (MapLevel.le a b)
  | .zero, _ => isTrue trivial
  | .one, .one | .one, .twoA | .one, .twoB | .one, .three | .one, .four => isTrue trivial
  | .twoA, .twoA | .twoA, .three | .twoA, .four => isTrue trivial
  | .twoB, .twoB | .twoB, .three | .twoB, .four => isTrue trivial
  | .three, .three | .three, .four => isTrue trivial
  | .four, .four => isTrue trivial
  | .one, .zero => isFalse fun h => h
  | .twoA, .zero | .twoA, .one | .twoA, .twoB => isFalse fun h => h
  | .twoB, .zero | .twoB, .one | .twoB, .twoA => isFalse fun h => h
  | .three, .zero | .three, .one | .three, .twoA | .three, .twoB => isFalse fun h => h
  | .four, .zero | .four, .one | .four, .twoA | .four, .twoB | .four, .three =>
      isFalse fun h => h

/-- Comparison in the finite map-level lattice is decidable. -/
instance : DecidableLE MapLevel := MapLevel.decLe

/-- The graph-to-relation level does not weaken to the relation-to-graph level. -/
theorem not_twoA_le_twoB : ¬ MapLevel.twoA ≤ MapLevel.twoB := by
  intro h
  exact h

/-- The relation-to-graph level does not weaken to the graph-to-relation level. -/
theorem not_twoB_le_twoA : ¬ MapLevel.twoB ≤ MapLevel.twoA := by
  intro h
  exact h

/-- The uniformly indexed form of the six one-direction map classes. -/
inductive MapClass {A : Type u} {B : Type v} (R : A → B → Sort w) :
    MapLevel → Type (max u v w) where
  /-- A bare relation with no additional directional data. -/
  | zero : MapClass R .zero
  /-- An otherwise unconstrained forward map. -/
  | one (data : MapClass1 R) : MapClass R .one
  /-- A map whose graph implies the relation. -/
  | twoA (data : MapClass2a R) : MapClass R .twoA
  /-- A map for which the relation implies graph equality. -/
  | twoB (data : MapClass2b R) : MapClass R .twoB
  /-- A map whose graph and relation imply one another. -/
  | three (data : MapClass3 R) : MapClass R .three
  /-- A level-`3` map with proof-relevant witness coherence. -/
  | four (data : MapClass4 R) : MapClass R .four

/-- A relation annotation pairs forward and backward map-class levels. -/
structure Annotation where
  /-- Structure available from the relation's left carrier to its right carrier. -/
  forward : MapLevel
  /-- Structure available from the converse relation's left carrier to its right carrier. -/
  backward : MapLevel
  deriving DecidableEq, Repr

/-- Annotations use the componentwise product order. -/
instance : PartialOrder Annotation where
  le α β := α.forward ≤ β.forward ∧ α.backward ≤ β.backward
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ hαβ hβγ := ⟨le_trans hαβ.1 hβγ.1, le_trans hαβ.2 hβγ.2⟩
  le_antisymm α β hαβ hβα := by
    have hf : α.forward = β.forward := le_antisymm hαβ.1 hβα.1
    have hb : α.backward = β.backward := le_antisymm hαβ.2 hβα.2
    cases α
    cases β
    cases hf
    cases hb
    rfl

/-- Annotation comparison is componentwise comparison of its two map levels. -/
theorem Annotation.le_iff (α β : Annotation) :
    α ≤ β ↔ α.forward ≤ β.forward ∧ α.backward ≤ β.backward :=
  Iff.rfl

/-- Componentwise comparison of finite annotations is decidable. -/
instance : DecidableLE Annotation := fun α β =>
  inferInstanceAs (Decidable (α.forward ≤ β.forward ∧ α.backward ≤ β.backward))

/-- Swap the forward and backward components of an annotation. -/
def Annotation.swap (α : Annotation) : Annotation :=
  ⟨α.backward, α.forward⟩

/-- Swapping an annotation twice recovers the original annotation. -/
@[simp] theorem Annotation.swap_swap (α : Annotation) : α.swap.swap = α := by
  cases α
  rfl

/-- Decide whether data at `available` can be weakened to `required`. -/
def Annotation.canWeaken (available required : Annotation) : Bool :=
  decide (required ≤ available)

/-- Boolean annotation inference agrees with the annotation order. -/
theorem Annotation.canWeaken_eq_true_iff {available required : Annotation} :
    Annotation.canWeaken available required = true ↔ required ≤ available := by
  simp [Annotation.canWeaken]

/-- An indexed relation class pairs forward data with data for the converse relation. -/
def RelationClass {A : Type u} {B : Type v} (α : Annotation) (R : A → B → Sort w) :=
  MapClass R α.forward × MapClass (Converse R) α.backward

/-- A structured relation packages a type-valued relation with data at annotation `α`. -/
abbrev StructuredRelation (α : Annotation) (A : Type u) (B : Type v) :=
  Σ R : A → B → Type w, RelationClass α R

/-- The underlying type-valued relation of a structured relation. -/
abbrev StructuredRelation.rel {A : Type u} {B : Type v} {α : Annotation}
    (S : StructuredRelation α A B) : A → B → Type w :=
  S.1

/-- The annotation-indexed class data carried by a structured relation. -/
abbrev StructuredRelation.relationClass {A : Type u} {B : Type v} {α : Annotation}
    (S : StructuredRelation α A B) : RelationClass α S.rel :=
  S.2

/-- Reverse a structured relation and swap its forward and backward annotations. -/
def StructuredRelation.converse {A : Type u} {B : Type v} {α : Annotation}
    (S : StructuredRelation α A B) : StructuredRelation α.swap B A :=
  ⟨Converse S.rel, S.relationClass.2, S.relationClass.1⟩

/-- The relation underlying a converse package is the converse relation. -/
@[simp] theorem StructuredRelation.converse_rel {A : Type u} {B : Type v}
    {α : Annotation} (S : StructuredRelation α A B) :
    S.converse.rel = Converse S.rel :=
  rfl

/-- Reversing a structured relation twice recovers the original package. -/
@[simp] theorem StructuredRelation.converse_converse {A : Type u} {B : Type v}
    {α : Annotation} (S : StructuredRelation α A B) : S.converse.converse = S := by
  rfl

/-- Converse is an equivalence between oppositely annotated structured relations. -/
def StructuredRelation.converseEquiv {A : Type u} {B : Type v} (α : Annotation) :
    StructuredRelation α A B ≃ StructuredRelation α.swap B A where
  toFun := StructuredRelation.converse
  invFun := StructuredRelation.converse
  left_inv := StructuredRelation.converse_converse
  right_inv := StructuredRelation.converse_converse

/-- Forget level-`4` coherence and retain level `3`. -/
def MapClass4.toMapClass3 {A : Type u} {B : Type v} {R : A → B → Sort w}
    (h : MapClass4 R) : MapClass3 R :=
  ⟨h.map, h.graphToRel, h.relToGraph⟩

/-- For a proposition-valued relation, level-`3` data automatically has level-`4` coherence. -/
def MapClass3.toMapClass4OfProp {A : Type u} {B : Type v} {R : A → B → Prop}
    (h : MapClass3 R) : MapClass4 R where
  map := h.map
  graphToRel := h.graphToRel
  relToGraph := h.relToGraph
  coherent := fun _ _ _ => Subsingleton.elim _ _

/-- Retain only the graph-to-relation half of level `3`. -/
def MapClass3.toMapClass2a {A : Type u} {B : Type v} {R : A → B → Sort w}
    (h : MapClass3 R) : MapClass2a R :=
  ⟨h.map, h.graphToRel⟩

/-- Retain only the relation-to-graph half of level `3`. -/
def MapClass3.toMapClass2b {A : Type u} {B : Type v} {R : A → B → Sort w}
    (h : MapClass3 R) : MapClass2b R :=
  ⟨h.map, h.relToGraph⟩

/-- Forget the graph-to-relation law and retain the map at level `1`. -/
def MapClass2a.toMapClass1 {A : Type u} {B : Type v} {R : A → B → Sort w}
    (h : MapClass2a R) : MapClass1 R :=
  ⟨h.map⟩

/-- Forget the relation-to-graph law and retain the map at level `1`. -/
def MapClass2b.toMapClass1 {A : Type u} {B : Type v} {R : A → B → Sort w}
    (h : MapClass2b R) : MapClass1 R :=
  ⟨h.map⟩

/-- Covariant change of relation preserves the graph-to-relation branch. -/
def MapClass2a.mapRelation {A : Type u} {B : Type v} {R : A → B → Sort w}
    {S : A → B → Sort w'} (hRS : ∀ a b, R a b → S a b) (h : MapClass2a R) :
    MapClass2a S where
  map := h.map
  graphToRel a b hab := hRS a b (h.graphToRel a b hab)

/-- Contravariant change of relation preserves the relation-to-graph branch. -/
def MapClass2b.contramapRelation {A : Type u} {B : Type v} {R : A → B → Sort w}
    {S : A → B → Sort w'} (hSR : ∀ a b, S a b → R a b) (h : MapClass2b R) :
    MapClass2b S where
  map := h.map
  relToGraph a b hs := h.relToGraph a b (hSR a b hs)

/-- Existing semantic subsumption preserves exactly the covariant level-`2a` law. -/
def Subsumes.mapClass2a {A : Type u} {B : Type v} {R S : A → B → Prop}
    (hRS : Subsumes R S) (h : MapClass2a R) : MapClass2a S :=
  h.mapRelation hRS

/-- Forget a level-`1` map and retain the bare relation at level `0`. -/
def MapClass1.toMapClass0 {A : Type u} {B : Type v} {R : A → B → Sort w}
    (_h : MapClass1 R) : MapClass0 R :=
  ()

/-- Weaken indexed map-class data along the six-level partial order. -/
def MapClass.weaken {A : Type u} {B : Type v} {R : A → B → Sort w}
    {low high : MapLevel} (h : low ≤ high) : MapClass R high → MapClass R low := by
  intro data
  change MapLevel.le low high at h
  cases low <;> cases high <;>
    simp_all (config := { failIfUnchanged := false }) only [MapLevel.le]
  · exact .zero
  · exact .zero
  · exact .zero
  · exact .zero
  · exact .zero
  · exact .zero
  · exact data
  · cases data with
    | twoA data => exact .one data.toMapClass1
  · cases data with
    | twoB data => exact .one data.toMapClass1
  · cases data with
    | three data => exact .one data.toMapClass2a.toMapClass1
  · cases data with
    | four data => exact .one data.toMapClass3.toMapClass2a.toMapClass1
  · exact data
  · cases data with
    | three data => exact .twoA data.toMapClass2a
  · cases data with
    | four data => exact .twoA data.toMapClass3.toMapClass2a
  · exact data
  · cases data with
    | three data => exact .twoB data.toMapClass2b
  · cases data with
    | four data => exact .twoB data.toMapClass3.toMapClass2b
  · exact data
  · cases data with
    | four data => exact .three data.toMapClass3
  · exact data

/-- Project the represented map from any map class at or above level `1`. -/
def MapClass.mapOfOneLE {A : Type u} {B : Type v} {R : A → B → Sort w}
    {level : MapLevel} (data : MapClass R level) (h : MapLevel.one ≤ level) : A → B :=
  match data.weaken h with
  | .one mapData => mapData.map

/-- Weakening above level `1` preserves the represented map. -/
theorem MapClass.mapOfOneLE_weaken {A : Type u} {B : Type v} {R : A → B → Sort w}
    {low high : MapLevel} (h : low ≤ high) (data : MapClass R high)
    (hOne : MapLevel.one ≤ low) :
    (data.weaken h).mapOfOneLE hOne = data.mapOfOneLE (le_trans hOne h) := by
  change MapLevel.le low high at h
  change MapLevel.le .one low at hOne
  cases low <;> cases high <;>
    simp only [MapLevel.le] at h hOne <;>
    cases data <;> rfl

/-- Project the forward map carried by a relation class at a suitable annotation. -/
def RelationClass.map {A : Type u} {B : Type v} {R : A → B → Sort w}
    {α : Annotation} (data : RelationClass α R) (h : MapLevel.one ≤ α.forward) : A → B :=
  data.1.mapOfOneLE h

/-- Project the backward map carried by a relation class at a suitable annotation. -/
def RelationClass.comap {A : Type u} {B : Type v} {R : A → B → Sort w}
    {α : Annotation} (data : RelationClass α R) (h : MapLevel.one ≤ α.backward) : B → A :=
  data.2.mapOfOneLE h

/-- Project the forward map carried by a suitably annotated structured relation. -/
def StructuredRelation.map {A : Type u} {B : Type v} {α : Annotation}
    (relation : StructuredRelation α A B) (h : MapLevel.one ≤ α.forward) : A → B :=
  relation.relationClass.map h

/-- Project the backward map carried by a suitably annotated structured relation. -/
def StructuredRelation.comap {A : Type u} {B : Type v} {α : Annotation}
    (relation : StructuredRelation α A B) (h : MapLevel.one ≤ α.backward) : B → A :=
  relation.relationClass.comap h

/-- The forward map of a converse structured relation is the original backward map. -/
@[simp] theorem StructuredRelation.converse_map {A : Type u} {B : Type v}
    {α : Annotation} (S : StructuredRelation α A B)
    (h : MapLevel.one ≤ α.backward) : S.converse.map h = S.comap h :=
  rfl

/-- The backward map of a converse structured relation is the original forward map. -/
@[simp] theorem StructuredRelation.converse_comap {A : Type u} {B : Type v}
    {α : Annotation} (S : StructuredRelation α A B)
    (h : MapLevel.one ≤ α.forward) : S.converse.comap h = S.map h :=
  rfl

/-- Weaken both directions of a relation class componentwise along the annotation order. -/
def RelationClass.weaken {A : Type u} {B : Type v} {R : A → B → Sort w}
    {low high : Annotation} (h : low ≤ high) (data : RelationClass high R) :
    RelationClass low R :=
  ⟨data.1.weaken h.1, data.2.weaken h.2⟩

/-- Annotation weakening that retains forward level `1` preserves the forward map. -/
theorem RelationClass.map_weaken {A : Type u} {B : Type v} {R : A → B → Sort w}
    {low high : Annotation} (h : low ≤ high) (data : RelationClass high R)
    (hOne : MapLevel.one ≤ low.forward) :
    (data.weaken h).map hOne = data.map (le_trans hOne h.1) :=
  MapClass.mapOfOneLE_weaken h.1 data.1 hOne

/-- Annotation weakening that retains backward level `1` preserves the backward map. -/
theorem RelationClass.comap_weaken {A : Type u} {B : Type v} {R : A → B → Sort w}
    {low high : Annotation} (h : low ≤ high) (data : RelationClass high R)
    (hOne : MapLevel.one ≤ low.backward) :
    (data.weaken h).comap hOne = data.comap (le_trans hOne h.2) :=
  MapClass.mapOfOneLE_weaken h.2 data.2 hOne

/-- Weaken a structured relation's class data while preserving its underlying relation. -/
def StructuredRelation.weaken {A : Type u} {B : Type v} {low high : Annotation}
    (h : low ≤ high) (S : StructuredRelation high A B) : StructuredRelation low A B :=
  ⟨S.rel, S.relationClass.weaken h⟩

/-- Weakening a structured relation leaves its underlying relation definitionally unchanged. -/
@[simp] theorem StructuredRelation.rel_weaken {A : Type u} {B : Type v}
    {low high : Annotation} (h : low ≤ high) (S : StructuredRelation high A B) :
    (S.weaken h).rel = S.rel :=
  rfl

/-- The class data of a weakened structured relation is componentwise weakening. -/
theorem StructuredRelation.relationClass_weaken {A : Type u} {B : Type v}
    {low high : Annotation} (h : low ≤ high) (S : StructuredRelation high A B) :
    (S.weaken h).relationClass = S.relationClass.weaken h :=
  rfl

/-- Weakening a structured relation above forward level `1` preserves its forward map. -/
theorem StructuredRelation.map_weaken {A : Type u} {B : Type v}
    {low high : Annotation} (h : low ≤ high) (S : StructuredRelation high A B)
    (hOne : MapLevel.one ≤ low.forward) :
    (S.weaken h).map hOne = S.map (le_trans hOne h.1) :=
  RelationClass.map_weaken h S.relationClass hOne

/-- Weakening a structured relation above backward level `1` preserves its backward map. -/
theorem StructuredRelation.comap_weaken {A : Type u} {B : Type v}
    {low high : Annotation} (h : low ≤ high) (S : StructuredRelation high A B)
    (hOne : MapLevel.one ≤ low.backward) :
    (S.weaken h).comap hOne = S.comap (le_trans hOne h.2) :=
  RelationClass.comap_weaken h S.relationClass hOne

/-- A separate proof-producing decision procedure weakens relation data when the requested
annotation lies below the available annotation. -/
def RelationClass.weaken? {A : Type u} {B : Type v} {R : A → B → Sort w}
    (available required : Annotation) (data : RelationClass available R) :
    Option (RelationClass required R) :=
  if h : required ≤ available then some (data.weaken h) else none

/-- Successful decidable weakening is equivalent to comparison in the annotation order. -/
theorem RelationClass.weaken?_isSome_iff {A : Type u} {B : Type v}
    {R : A → B → Sort w} (available required : Annotation)
    (data : RelationClass available R) :
    (RelationClass.weaken? available required data).isSome ↔ required ≤ available := by
  simp [RelationClass.weaken?]

/-- A functional denotation relation canonically carries the strongest forward map class. -/
def denoteMapClass4 {C : Type u} {A : Type v} (denote : C → A) :
    MapClass4 (DenoteRel denote) where
  map := denote
  graphToRel := fun _ _ h => h
  relToGraph := fun _ _ h => h
  coherent := fun _ _ _ => rfl

/-- A denotation graph carries level `4` forward data and no assumed backward data. -/
def denoteRelationClass {C : Type u} {A : Type v} (denote : C → A) :
    RelationClass ⟨.four, .zero⟩ (DenoteRel denote) :=
  ⟨.four (denoteMapClass4 denote), .zero⟩

/-- Two level-`3` directions package the relation and converse around mutually inverse maps. -/
structure BiMapClass3 {A : Type u} {B : Type v} (R : A → B → Sort w) where
  /-- The level-`3` structure in the forward direction. -/
  forward : MapClass3 R
  /-- The level-`3` structure on the converse relation. -/
  backward : MapClass3 (Converse R)

/-- A bidirectional level-`3` relation determines an equivalence of its carrier types. -/
def BiMapClass3.toEquiv {A : Type u} {B : Type v} {R : A → B → Sort w}
    (h : BiMapClass3 R) : Equiv A B where
  toFun := h.forward.map
  invFun := h.backward.map
  left_inv _ := h.backward.relToGraph _ _ (h.forward.graphToRel _ _ rfl)
  right_inv _ := h.forward.relToGraph _ _ (h.backward.graphToRel _ _ rfl)

/-- The annotation for a bare relation carrying an arbitrary forward function. -/
def Annotation.function : Annotation := ⟨.one, .zero⟩

/-- The annotation for a coherent represented map without a backward map. -/
def Annotation.univalentMap : Annotation := ⟨.four, .zero⟩

/-- The annotation for a coherent represented map with a graph-to-relation backward map. -/
def Annotation.retraction : Annotation := ⟨.four, .twoA⟩

/-- The annotation for a coherent represented map with a relation-to-graph backward map. -/
def Annotation.section : Annotation := ⟨.four, .twoB⟩

/-- The annotation for a relation represented coherently in both directions. -/
def Annotation.equivalence : Annotation := ⟨.four, .four⟩

/-- The annotation for a relation represented in both directions without witness coherence. -/
def Annotation.isomorphism : Annotation := ⟨.three, .three⟩

/-- A level allowed on the universe translation's weak, non-univalent side. -/
def MapLevel.IsUniverseWeak : MapLevel → Prop
  | .zero | .one | .twoA => True
  | .twoB | .three | .four => False

/-- Both directions of an annotation lie in the universe translation's weak fragment. -/
def Annotation.IsUniverseWeak (α : Annotation) : Prop :=
  α.forward.IsUniverseWeak ∧ α.backward.IsUniverseWeak

/-- A pair of annotations is admissible for translating universes when the source is fully
equivalent or the target asks only for weak graph-producing structure. -/
def AdmissibleUniverseTranslation (source target : Annotation) : Prop :=
  source = Annotation.equivalence ∨ target.IsUniverseWeak

/-- A fully coherent source annotation permits every target annotation for universe translation. -/
theorem admissibleUniverseTranslation_of_equivalence (target : Annotation) :
    AdmissibleUniverseTranslation Annotation.equivalence target :=
  Or.inl rfl

/-- A weak target annotation permits every source annotation for universe translation. -/
theorem admissibleUniverseTranslation_of_weak {source target : Annotation}
    (h : target.IsUniverseWeak) : AdmissibleUniverseTranslation source target :=
  Or.inr h

/-- A `(1, 0)` relation class exposes its arbitrary forward function. -/
def RelationClass.toFunction {A : Type u} {B : Type v} {R : A → B → Sort w}
    (h : RelationClass Annotation.function R) : A → B := by
  cases h.1 with
  | one data => exact data.map

/-- A `(4, 0)` relation class is a coherent represented map. -/
def RelationClass.toUnivalentMap {A : Type u} {B : Type v} {R : A → B → Sort w}
    (h : RelationClass Annotation.univalentMap R) : MapClass4 R := by
  cases h.1 with
  | four data => exact data

/-- The maps and right-inverse law exposed by a retraction annotation. -/
structure RetractionData (A : Type u) (B : Type v) where
  /-- The forward map. -/
  map : A → B
  /-- The chosen inverse map. -/
  inverse : B → A
  /-- The chosen inverse is a right inverse of the forward map. -/
  rightInverse : Function.RightInverse inverse map

/-- The maps and left-inverse law exposed by a section annotation. -/
structure SectionData (A : Type u) (B : Type v) where
  /-- The forward map. -/
  map : A → B
  /-- The chosen inverse map. -/
  inverse : B → A
  /-- The chosen inverse is a left inverse of the forward map. -/
  leftInverse : Function.LeftInverse inverse map

/-- A `(4, 2a)` relation class supplies a right inverse to its forward map. -/
def RelationClass.toRightInverse {A : Type u} {B : Type v} {R : A → B → Sort w}
    (h : RelationClass Annotation.retraction R) : RetractionData A B := by
  cases h.1 with
  | four forward =>
    cases h.2 with
    | twoA backward =>
      exact ⟨forward.map, backward.map, fun b =>
        forward.relToGraph _ _ (backward.graphToRel _ _ rfl)⟩

/-- A `(4, 2b)` relation class supplies a left inverse to its forward map. -/
def RelationClass.toLeftInverse {A : Type u} {B : Type v} {R : A → B → Sort w}
    (h : RelationClass Annotation.section R) : SectionData A B := by
  cases h.1 with
  | four forward =>
    cases h.2 with
    | twoB backward =>
      exact ⟨forward.map, backward.map, fun a =>
        backward.relToGraph _ _ (forward.graphToRel _ _ rfl)⟩

/-- A `(4, 4)` relation class determines an equivalence of its carrier types. -/
def RelationClass.equivalenceToEquiv {A : Type u} {B : Type v} {R : A → B → Sort w}
    (h : RelationClass Annotation.equivalence R) : A ≃ B := by
  cases h.1 with
  | four forward =>
    cases h.2 with
    | four backward =>
      exact BiMapClass3.toEquiv
        { forward := forward.toMapClass3, backward := backward.toMapClass3 }

/-- A `(3, 3)` relation class determines an isomorphism of its carrier types. -/
def RelationClass.isomorphismToEquiv {A : Type u} {B : Type v} {R : A → B → Sort w}
    (h : RelationClass Annotation.isomorphism R) : A ≃ B := by
  cases h.1 with
  | three forward =>
    cases h.2 with
    | three backward =>
      exact BiMapClass3.toEquiv { forward := forward, backward := backward }

example : AdmissibleUniverseTranslation Annotation.equivalence Annotation.isomorphism :=
  admissibleUniverseTranslation_of_equivalence _

example : AdmissibleUniverseTranslation Annotation.function ⟨.twoA, .one⟩ :=
  admissibleUniverseTranslation_of_weak ⟨trivial, trivial⟩

example {A : Type u} {B : Type v} (α : Annotation) :
    StructuredRelation.{u, v, w} α A B = (Σ R : A → B → Type w, RelationClass α R) :=
  rfl

example {A : Type u} {B : Type v} (α : Annotation) :
    StructuredRelation.{u, v, w} α A B ≃ StructuredRelation.{v, u, w} α.swap B A :=
  StructuredRelation.converseEquiv α

example {A : Type u} {B : Type v} {low high : Annotation} (h : low ≤ high)
    (S : StructuredRelation high A B) : (S.weaken h).rel = S.rel :=
  rfl

example (α β : Annotation) :
    α ≤ β ↔ α.forward ≤ β.forward ∧ α.backward ≤ β.backward :=
  Annotation.le_iff α β

example {A : Type u} {B : Type v} {α : Annotation}
    (S : StructuredRelation α A B) (h : MapLevel.one ≤ α.forward) : A → B :=
  S.map h

example {A : Type u} {B : Type v} {α : Annotation}
    (S : StructuredRelation α A B) (h : MapLevel.one ≤ α.backward) : B → A :=
  S.comap h

example {A : Type u} {B : Type v} {α : Annotation}
    (S : StructuredRelation α A B) (h : MapLevel.one ≤ α.backward) :
    S.converse.map h = S.comap h :=
  StructuredRelation.converse_map S h

example {A : Type u} {B : Type v} {α : Annotation}
    (S : StructuredRelation α A B) (h : MapLevel.one ≤ α.forward) :
    S.converse.comap h = S.map h :=
  StructuredRelation.converse_comap S h

example {A : Type u} {B : Type v} {R : A → B → Sort w}
    {low high : MapLevel} (h : low ≤ high) (data : MapClass R high)
    (hOne : MapLevel.one ≤ low) :
    (data.weaken h).mapOfOneLE hOne = data.mapOfOneLE (le_trans hOne h) :=
  MapClass.mapOfOneLE_weaken h data hOne

example {A : Type u} {B : Type v} {R : A → B → Sort w}
    {low high : Annotation} (h : low ≤ high) (data : RelationClass high R)
    (hOne : MapLevel.one ≤ low.forward) :
    (data.weaken h).map hOne = data.map (le_trans hOne h.1) :=
  RelationClass.map_weaken h data hOne

example {A : Type u} {B : Type v} {R : A → B → Sort w}
    {low high : Annotation} (h : low ≤ high) (data : RelationClass high R)
    (hOne : MapLevel.one ≤ low.backward) :
    (data.weaken h).comap hOne = data.comap (le_trans hOne h.2) :=
  RelationClass.comap_weaken h data hOne

example {A : Type u} {B : Type v} {low high : Annotation} (h : low ≤ high)
    (S : StructuredRelation high A B) (hOne : MapLevel.one ≤ low.forward) :
    (S.weaken h).map hOne = S.map (le_trans hOne h.1) :=
  StructuredRelation.map_weaken h S hOne

example {A : Type u} {B : Type v} {low high : Annotation} (h : low ≤ high)
    (S : StructuredRelation high A B) (hOne : MapLevel.one ≤ low.backward) :
    (S.weaken h).comap hOne = S.comap (le_trans hOne h.2) :=
  StructuredRelation.comap_weaken h S hOne

end DeepWiki.Refine
