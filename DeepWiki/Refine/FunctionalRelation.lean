import DeepWiki.Refine.RelationStructure
import DeepWiki.Refine.TypeEquivalence

/-! # Functional proof-relevant relations

Contractible fibers characterize relations carrying a coherent forward map. Bidirectional
functionality then gives a symmetric presentation of equivalence. -/

namespace DeepWiki.Refine

universe u v w

/-- `IsContr T` packages a center of `T` and a path from that center to every point. -/
structure IsContr (T : Type u) where
  /-- The distinguished center of the contractible type. -/
  center : T
  /-- Every point equals the center, in the chosen outward orientation. -/
  contraction : ∀ point, center = point

/-- The equality graph of a function, lifted into an arbitrary relation universe. -/
abbrev EqualityGraph {A : Type u} {B : Type v} (f : A → B) (a : A) (b : B) :=
  ULift.{w} (PLift (f a = b))

/-- Contractibility witnesses are determined by their centers. -/
@[ext] theorem IsContr.ext {T : Type u} {x y : IsContr T} (h : x.center = y.center) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Contractibility evidence for a fixed type is unique. -/
theorem isContr_subsingleton (T : Type u) : Subsingleton (IsContr T) := by
  constructor
  intro left right
  exact IsContr.ext (left.contraction right.center)

/-- A proof-relevant relation is functional when every left fiber is contractible. -/
def IsFun {A : Type u} {B : Type v} (R : A → B → Type w) : Type (max u v w) :=
  ∀ a, IsContr (Σ b, R a b)

/-- Functionality evidence for a fixed relation is unique. -/
theorem isFun_subsingleton {A : Type u} {B : Type v} (R : A → B → Type w) :
    Subsingleton (IsFun R) := by
  constructor
  intro left right
  funext a
  exact (isContr_subsingleton _).elim _ _

/-- Transport the second component of a dependent pair along an equality of first components. -/
def sigmaSndTransport {A : Type u} {B : A → Type v} {x y : Sigma B} (h : x = y) : B y.1 :=
  Eq.ndrec x.2 (congrArg Sigma.fst h)

/-- Transport induced by an equality of dependent pairs recovers the target second component. -/
theorem sigmaSndTransport_eq {A : Type u} {B : A → Type v} {x y : Sigma B} (h : x = y) :
    sigmaSndTransport h = y.2 := by
  cases h
  rfl

/-- Transporting a canonical dependent witness agrees with applying its constructor to the path. -/
theorem graphToRel_transport {A : Type u} {B : Type v} {R : A → B → Type w}
    (map : A → B) (graphToRel : GraphToRel R map) (a : A) (b : B) (h : map a = b) :
    Eq.ndrec (graphToRel a (map a) rfl) h = graphToRel a b h := by
  cases h
  rfl

/-- A univalent map is the level-`4` one-direction structure on a relation. -/
abbrev IsUmap {A : Type u} {B : Type v} (R : A → B → Type w) := MapClass4 R

/-- A function's equality graph carries the canonical coherent represented map. -/
def equalityGraphIsUmap (f : A → B) : IsUmap (EqualityGraph.{u, v, w} f) where
  map := f
  graphToRel := fun _ _ path => ⟨⟨path⟩⟩
  relToGraph := fun _ _ related => related.down.down
  coherent := fun _ _ _ => Subsingleton.elim _ _

/-- The equality graph of a map with a chosen right inverse carries retraction structure. -/
def rightInverseStructuredRelation {A : Type u} {B : Type v}
    (forward : A → B) (backward : B → A)
    (rightInverse : Function.RightInverse backward forward) :
    StructuredRelation.{u, v, w} Annotation.retraction A B :=
  ⟨EqualityGraph forward,
    .four (equalityGraphIsUmap forward),
    .twoA
      { map := backward
        graphToRel := fun b _a hba =>
          ⟨⟨(congrArg forward hba).symm.trans (rightInverse b)⟩⟩ }⟩

/-- The structured right-inverse relation projects to the forward equality graph. -/
@[simp] theorem rightInverseStructuredRelation_rel {A : Type u} {B : Type v}
    (forward : A → B) (backward : B → A)
    (rightInverse : Function.RightInverse backward forward) :
    (rightInverseStructuredRelation.{u, v, w} forward backward rightInverse).rel =
      EqualityGraph forward :=
  rfl

/-- A coherent represented relation is fiberwise equivalent to its map's equality graph. -/
def IsUmap.relationEquivEqualityGraph {A : Type u} {B : Type v}
    {R : A → B → Type w} (h : IsUmap R) (a : A) (b : B) :
    R a b ≃ EqualityGraph.{u, v, w} h.map a b where
  toFun related := ⟨⟨h.relToGraph a b related⟩⟩
  invFun path := h.graphToRel a b path.down.down
  left_inv := h.coherent a b
  right_inv := fun _ => Subsingleton.elim _ _

/-- Contractible fibers determine a coherent map represented by the relation. -/
def IsFun.toIsUmap {A : Type u} {B : Type v} {R : A → B → Type w}
    (h : IsFun R) : IsUmap R where
  map a := (h a).center.1
  graphToRel a b hab := Eq.ndrec (h a).center.2 hab
  relToGraph a b r := congrArg Sigma.fst ((h a).contraction ⟨b, r⟩)
  coherent a b r := by
    let path : (h a).center = ⟨b, r⟩ := (h a).contraction ⟨b, r⟩
    exact sigmaSndTransport_eq path

/-- A coherent represented map makes each fiber of its relation contractible. -/
def IsUmap.toIsFun {A : Type u} {B : Type v} {R : A → B → Type w}
    (h : IsUmap R) : IsFun R := fun a =>
  { center := ⟨h.map a, h.graphToRel a (h.map a) rfl⟩
    contraction := fun point => by
      rcases point with ⟨b, r⟩
      let path := h.relToGraph a b r
      apply Sigma.ext path
      exact (eqRec_heq path (h.graphToRel a (h.map a) rfl)).symm.trans
        (heq_of_eq ((graphToRel_transport h.map h.graphToRel a b path).trans
          (h.coherent a b r))) }

/-- Every contractibility witness is recovered after conversion through a univalent map. -/
theorem IsFun.toIsUmap_toIsFun {A : Type u} {B : Type v} {R : A → B → Type w}
    (h : IsFun R) : h.toIsUmap.toIsFun = h := by
  funext a
  apply IsContr.ext
  rfl

/-- Level-`4` structures are determined by their maps and graph-to-relation operations. -/
theorem MapClass4.ext {A : Type u} {B : Type v} {R : A → B → Type w}
    {x y : MapClass4 R} (hmap : x.map = y.map)
    (hgraph : HEq x.graphToRel y.graphToRel) : x = y := by
  cases x
  cases y
  cases hmap
  cases eq_of_heq hgraph
  rfl

/-- Every univalent-map witness is recovered after conversion through contractible fibers. -/
theorem IsUmap.toIsFun_toIsUmap {A : Type u} {B : Type v} {R : A → B → Type w}
    (h : IsUmap R) : h.toIsFun.toIsUmap = h := by
  apply MapClass4.ext (x := h.toIsFun.toIsUmap) (y := h) rfl
  apply heq_of_eq
  funext a b path
  exact graphToRel_transport h.map h.graphToRel a b path

/-- Functional relations and univalent maps are equivalent structures. -/
def isFunEquivIsUmap {A : Type u} {B : Type v} (R : A → B → Type w) :
    IsFun R ≃ IsUmap R where
  toFun := IsFun.toIsUmap
  invFun := IsUmap.toIsFun
  left_inv := IsFun.toIsUmap_toIsFun
  right_inv := IsUmap.toIsFun_toIsUmap

/-- A proof-relevant relation together with contractibility of every left fiber. -/
structure FunctionalRelation (A : Type u) (B : Type v) where
  /-- The proof-relevant relation represented by a function. -/
  rel : A → B → Type w
  /-- Every fiber of the relation is contractible. -/
  functional : IsFun rel

/-- Functional-relation packages agree when their relation families agree. -/
@[ext] theorem FunctionalRelation.ext {A : Type u} {B : Type v}
    {left right : FunctionalRelation.{u, v, w} A B} (rel_eq : left.rel = right.rel) :
    left = right := by
  cases left
  cases right
  cases rel_eq
  congr
  exact (isFun_subsingleton _).elim _ _

/-- The dependent-pair presentation of a functional relation. -/
abbrev FunctionalRelationData (A : Type u) (B : Type v) :=
  Σ R : A → B → Type w, IsFun R

/-- Structure and sigma presentations of functional relations are equivalent. -/
def functionalRelationEquivData (A : Type u) (B : Type v) :
    FunctionalRelation.{u, v, w} A B ≃ FunctionalRelationData.{u, v, w} A B where
  toFun relation := ⟨relation.rel, relation.functional⟩
  invFun relation := ⟨relation.1, relation.2⟩
  left_inv := fun relation => by cases relation; rfl
  right_inv := fun relation => by cases relation; rfl

/-- A function determines the functional relation given by its equality graph. -/
def FunctionalRelation.ofFunction (f : A → B) : FunctionalRelation.{u, v, w} A B where
  rel := EqualityGraph.{u, v, w} f
  functional := (equalityGraphIsUmap.{u, v, w} f).toIsFun

/-- A functional relation exposes the function at the center of each contractible fiber. -/
def FunctionalRelation.toFunction {A : Type u} {B : Type v}
    (relation : FunctionalRelation.{u, v, w} A B) : A → B :=
  relation.functional.toIsUmap.map

/-- Recovering the function represented by its equality graph is definitionally pointwise. -/
theorem FunctionalRelation.toFunction_ofFunction (f : A → B) :
    (FunctionalRelation.ofFunction.{u, v, w} f).toFunction = f :=
  rfl

/-- Under univalence, a functional relation family equals its represented equality graph. -/
theorem FunctionalRelation.rel_eq_equalityGraph (univalent : IsUnivalentUniverse.{w})
    {A : Type u} {B : Type v} (relation : FunctionalRelation.{u, v, w} A B) :
    relation.rel = EqualityGraph.{u, v, w} relation.toFunction := by
  funext a b
  exact univalent.pathOfEquivalence
    (relation.functional.toIsUmap.relationEquivEqualityGraph a b)

/-- Assuming univalence, functions are equivalent to proof-relevant functional relations. -/
def functionEquivFunctionalRelation (univalent : IsUnivalentUniverse.{w})
    (A : Type u) (B : Type v) : (A → B) ≃ FunctionalRelation.{u, v, w} A B where
  toFun := FunctionalRelation.ofFunction
  invFun := FunctionalRelation.toFunction
  left_inv := FunctionalRelation.toFunction_ofFunction
  right_inv := fun relation => by
    apply FunctionalRelation.ext
    exact relation.rel_eq_equalityGraph univalent |>.symm

/-- Assuming univalence, functions are equivalent to dependent pairs of functional relations. -/
def functionEquivFunctionalRelationData (univalent : IsUnivalentUniverse.{w})
    (A : Type u) (B : Type v) : (A → B) ≃ FunctionalRelationData.{u, v, w} A B :=
  (functionEquivFunctionalRelation univalent A B).trans (functionalRelationEquivData A B)

/-- The symmetric functional-relation presentation of an equivalence. -/
structure FunctionalEquivalence (A : Type u) (B : Type v) where
  /-- The heterogeneous relation mediating the equivalence. -/
  rel : A → B → Type w
  /-- Every forward fiber is contractible. -/
  forward : IsFun rel
  /-- Every backward fiber is contractible. -/
  backward : IsFun (Converse rel)

/-- An ordinary equivalence determines a relation functional in both directions. -/
def FunctionalEquivalence.ofEquiv {A : Type u} {B : Type v} (e : A ≃ B) :
    FunctionalEquivalence.{u, v, w} A B where
  rel := EqualityGraph.{u, v, w} e
  forward := (equalityGraphIsUmap.{u, v, w} e).toIsFun
  backward :=
    (show IsUmap (Converse (EqualityGraph.{u, v, w} e)) from
      { map := e.symm
        graphToRel := fun b a path =>
          ⟨⟨(congrArg e path).symm.trans (e.apply_symm_apply b)⟩⟩
        relToGraph := fun a b related =>
          (congrArg e.symm related.down.down).symm.trans (e.symm_apply_apply b)
        coherent := fun _ _ related => by
          exact congrArg ULift.up (congrArg PLift.up (Subsingleton.elim _ _)) }).toIsFun

/-- A relation functional in both directions determines an ordinary equivalence. -/
def FunctionalEquivalence.toEquiv {A : Type u} {B : Type v}
    (h : FunctionalEquivalence.{u, v, w} A B) : A ≃ B :=
  (BiMapClass3.toEquiv
    { forward := h.forward.toIsUmap.toMapClass3
      backward := h.backward.toIsUmap.toMapClass3 })

/-- Converting an ordinary equivalence to a bidirectionally functional relation recovers its map. -/
theorem FunctionalEquivalence.ofEquiv_toEquiv {A : Type u} {B : Type v} (e : A ≃ B) :
    (FunctionalEquivalence.ofEquiv.{u, v, w} e).toEquiv = e := by
  ext a
  rfl

/-- Bidirectionally functional packages agree when their relation families agree. -/
@[ext] theorem FunctionalEquivalence.ext {A : Type u} {B : Type v}
    {left right : FunctionalEquivalence.{u, v, w} A B} (rel_eq : left.rel = right.rel) :
    left = right := by
  cases left
  cases right
  cases rel_eq
  congr
  · exact (isFun_subsingleton _).elim _ _
  · exact (isFun_subsingleton _).elim _ _

/-- The dependent-pair presentation of a relation functional in both directions. -/
abbrev BidirectionallyFunctionalRelationData (A : Type u) (B : Type v) :=
  Σ R : A → B → Type w, IsFun R × IsFun (Converse R)

/-- Structure and sigma presentations of bidirectionally functional relations are equivalent. -/
def functionalEquivalenceEquivData (A : Type u) (B : Type v) :
    FunctionalEquivalence.{u, v, w} A B ≃
      BidirectionallyFunctionalRelationData.{u, v, w} A B where
  toFun relation := ⟨relation.rel, relation.forward, relation.backward⟩
  invFun relation := ⟨relation.1, relation.2.1, relation.2.2⟩
  left_inv := fun relation => by cases relation; rfl
  right_inv := fun relation => by cases relation; rfl

/-- Under univalence, a bidirectionally functional relation equals its forward equality graph. -/
theorem FunctionalEquivalence.rel_eq_equalityGraph (univalent : IsUnivalentUniverse.{w})
    {A : Type u} {B : Type v} (relation : FunctionalEquivalence.{u, v, w} A B) :
    relation.rel = EqualityGraph.{u, v, w} relation.toEquiv := by
  funext a b
  exact univalent.pathOfEquivalence
    (relation.forward.toIsUmap.relationEquivEqualityGraph a b)

/-- Assuming univalence, equivalences are equivalent to bidirectionally functional relations. -/
def typeEquivalenceEquivFunctionalEquivalence (univalent : IsUnivalentUniverse.{w})
    (A : Type u) (B : Type v) : (A ≃ B) ≃ FunctionalEquivalence.{u, v, w} A B where
  toFun := FunctionalEquivalence.ofEquiv
  invFun := FunctionalEquivalence.toEquiv
  left_inv := FunctionalEquivalence.ofEquiv_toEquiv
  right_inv := fun relation => by
    apply FunctionalEquivalence.ext
    exact relation.rel_eq_equalityGraph univalent |>.symm

/-- Assuming univalence, type equivalence has a symmetric functional-relation form. -/
def typeEquivalenceEquivBidirectionallyFunctionalRelation
    (univalent : IsUnivalentUniverse.{w}) (A : Type u) (B : Type v) :
    (A ≃ B) ≃ BidirectionallyFunctionalRelationData.{u, v, w} A B :=
  (typeEquivalenceEquivFunctionalEquivalence univalent A B).trans
    (functionalEquivalenceEquivData A B)

/-- The symmetric relation type built from univalent maps in both directions. -/
abbrev BidirectionallyUnivalentRelationData (A : Type u) (B : Type v) :=
  Σ R : A → B → Type w, IsUmap R × IsUmap (Converse R)

/-- Bidirectionally functional relations and bidirectional univalent maps are equivalent data. -/
def bidirectionallyFunctionalEquivUnivalentRelation (A : Type u) (B : Type v) :
    BidirectionallyFunctionalRelationData.{u, v, w} A B ≃
      BidirectionallyUnivalentRelationData.{u, v, w} A B where
  toFun relation := ⟨relation.1, relation.2.1.toIsUmap, relation.2.2.toIsUmap⟩
  invFun relation := ⟨relation.1, relation.2.1.toIsFun, relation.2.2.toIsFun⟩
  left_inv := fun relation => by
    rcases relation with ⟨R, forward, backward⟩
    have hf : forward.toIsUmap.toIsFun = forward := forward.toIsUmap_toIsFun
    have hb : backward.toIsUmap.toIsFun = backward := backward.toIsUmap_toIsFun
    exact Sigma.ext rfl (heq_of_eq (Prod.ext hf hb))
  right_inv := fun relation => by
    rcases relation with ⟨R, forward, backward⟩
    have hf : forward.toIsFun.toIsUmap = forward := forward.toIsFun_toIsUmap
    have hb : backward.toIsFun.toIsUmap = backward := backward.toIsFun_toIsUmap
    exact Sigma.ext rfl (heq_of_eq (Prod.ext hf hb))

/-- Raw bidirectional level-`4` data is equivalent to the top structured-relation package. -/
def bidirectionallyUnivalentEquivStructuredRelation (A : Type u) (B : Type v) :
    BidirectionallyUnivalentRelationData.{u, v, w} A B ≃
      StructuredRelation.{u, v, w} Annotation.equivalence A B where
  toFun relation :=
    ⟨relation.1, .four relation.2.1, .four relation.2.2⟩
  invFun relation := by
    rcases relation with ⟨R, forward, backward⟩
    cases forward with
    | four forward =>
      cases backward with
      | four backward => exact ⟨R, forward, backward⟩
  left_inv := fun relation => by
    rcases relation with ⟨R, forward, backward⟩
    rfl
  right_inv := fun relation => by
    rcases relation with ⟨R, forward, backward⟩
    cases forward with
    | four forward =>
      cases backward with
      | four backward => rfl

/-- Assuming univalence, equivalence is a symmetric pair of univalent maps. -/
def typeEquivalenceEquivBidirectionallyUnivalentRelation
    (univalent : IsUnivalentUniverse.{w}) (A : Type u) (B : Type v) :
    (A ≃ B) ≃ BidirectionallyUnivalentRelationData.{u, v, w} A B :=
  (typeEquivalenceEquivBidirectionallyFunctionalRelation univalent A B).trans
    (bidirectionallyFunctionalEquivUnivalentRelation A B)

/-- Assuming univalence, equivalence is the top structured-relation type. -/
def typeEquivalenceEquivStructuredRelationTop
    (univalent : IsUnivalentUniverse.{w}) (A : Type u) (B : Type v) :
    (A ≃ B) ≃ StructuredRelation.{u, v, w} Annotation.equivalence A B :=
  (typeEquivalenceEquivBidirectionallyUnivalentRelation univalent A B).trans
    (bidirectionallyUnivalentEquivStructuredRelation A B)

/-- Types admit a bidirectionally functional relation exactly when they are equivalent. -/
theorem nonempty_functionalEquivalence_iff {A : Type u} {B : Type v} :
    Nonempty (FunctionalEquivalence.{u, v, w} A B) ↔ Nonempty (A ≃ B) :=
  ⟨fun ⟨h⟩ => ⟨h.toEquiv⟩,
    fun ⟨e⟩ => ⟨FunctionalEquivalence.ofEquiv.{u, v, w} e⟩⟩

example {A : Type u} {B : Type v} (R : A → B → Type w) : IsFun R ≃ IsUmap R :=
  isFunEquivIsUmap R

example {A : Type u} {B : Type v} (h : FunctionalEquivalence.{u, v, w} A B) : A ≃ B :=
  h.toEquiv

example (univalent : IsUnivalentUniverse.{w}) (A : Type u) (B : Type v) :
    (A → B) ≃ FunctionalRelationData.{u, v, w} A B :=
  functionEquivFunctionalRelationData univalent A B

example (univalent : IsUnivalentUniverse.{w}) (A : Type u) (B : Type v) :
    (A ≃ B) ≃ BidirectionallyFunctionalRelationData.{u, v, w} A B :=
  typeEquivalenceEquivBidirectionallyFunctionalRelation univalent A B

example (univalent : IsUnivalentUniverse.{w}) (A : Type u) (B : Type v) :
    (A ≃ B) ≃ BidirectionallyUnivalentRelationData.{u, v, w} A B :=
  typeEquivalenceEquivBidirectionallyUnivalentRelation univalent A B

example (univalent : IsUnivalentUniverse.{w}) (A : Type u) (B : Type v) :
    (A ≃ B) ≃ StructuredRelation.{u, v, w} Annotation.equivalence A B :=
  typeEquivalenceEquivStructuredRelationTop univalent A B

end DeepWiki.Refine
