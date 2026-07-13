import DeepWiki.Refine.RelationStructure

/-! # Functional proof-relevant relations

Contractible fibers characterize relations carrying a coherent forward map. Bidirectional
functionality then gives a symmetric presentation of equivalence. -/

namespace DeepWiki.Refine

universe u v w

/-- `IsContr T` packages a center of `T` and a path from that center to every point. -/
structure IsContr (T : Type u) where
  /-- The distinguished center of the contractible type. -/
  center : T
  /-- Every point equals the center, in the outward orientation used by the paper. -/
  contraction : ∀ point, center = point

/-- Contractibility witnesses are determined by their centers. -/
@[ext] theorem IsContr.ext {T : Type u} {x y : IsContr T} (h : x.center = y.center) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- A proof-relevant relation is functional when every left fiber is contractible. -/
def IsFun {A : Type u} {B : Type v} (R : A → B → Type w) : Type (max u v w) :=
  ∀ a, IsContr (Σ b, R a b)

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

/-- The symmetric functional-relation presentation of an equivalence. -/
structure FunctionalEquivalence (A : Type u) (B : Type v) where
  /-- The heterogeneous relation mediating the equivalence. -/
  rel : A → B → Type
  /-- Every forward fiber is contractible. -/
  forward : IsFun rel
  /-- Every backward fiber is contractible. -/
  backward : IsFun (Converse rel)

/-- An ordinary equivalence determines a relation functional in both directions. -/
def FunctionalEquivalence.ofEquiv {A : Type u} {B : Type v} (e : A ≃ B) :
    FunctionalEquivalence A B where
  rel a b := PLift (e a = b)
  forward :=
    (show IsUmap (fun a b => PLift (e a = b)) from
      { map := e
        graphToRel := fun _ _ h => ⟨h⟩
        relToGraph := fun _ _ h => h.down
        coherent := fun _ _ h => by cases h; rfl }).toIsFun
  backward := fun b =>
    { center := ⟨e.symm b, ⟨e.apply_symm_apply b⟩⟩
      contraction := fun point => by
        rcases point with ⟨a, h⟩
        let ha : e.symm b = a :=
          e.injective ((e.apply_symm_apply b).trans h.down.symm)
        apply Sigma.ext ha
        cases ha
        apply heq_of_eq
        cases h
        congr }

/-- A relation functional in both directions determines an ordinary equivalence. -/
def FunctionalEquivalence.toEquiv {A : Type u} {B : Type v}
    (h : FunctionalEquivalence A B) : A ≃ B :=
  (BiMapClass3.toEquiv
    { forward := h.forward.toIsUmap.toMapClass3
      backward := h.backward.toIsUmap.toMapClass3 })

/-- Converting an ordinary equivalence to a bidirectionally functional relation recovers its map. -/
theorem FunctionalEquivalence.ofEquiv_toEquiv {A : Type u} {B : Type v} (e : A ≃ B) :
    (FunctionalEquivalence.ofEquiv e).toEquiv = e := by
  ext a
  rfl

/-- Types admit a bidirectionally functional relation exactly when they are equivalent. -/
theorem nonempty_functionalEquivalence_iff {A : Type u} {B : Type v} :
    Nonempty (FunctionalEquivalence A B) ↔ Nonempty (A ≃ B) :=
  ⟨fun ⟨h⟩ => ⟨h.toEquiv⟩, fun ⟨e⟩ => ⟨FunctionalEquivalence.ofEquiv e⟩⟩

example {A : Type u} {B : Type v} (R : A → B → Type w) : IsFun R ≃ IsUmap R :=
  isFunEquivIsUmap R

example {A : Type u} {B : Type v} (h : FunctionalEquivalence A B) : A ≃ B :=
  h.toEquiv

end DeepWiki.Refine
