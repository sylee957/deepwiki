import DeepWiki.Refine.Basic

/-! # Dependent relational products

The relational interpretations of dependent functions, dependent pairs, and lists extend the
first-order respectful arrow to binders and type constructors. -/

namespace DeepWiki.Refine

universe u v u' v' w w'

/-- The dependent respectful product relates functions whose outputs are related over every
related pair of inputs and its relation witness. -/
def DependentRespectful {A : Type u} {B : Type v} (R : A → B → Sort w)
    {C : A → Type u'} {D : B → Type v'}
    (S : ∀ a b, R a b → C a → D b → Sort w')
    (f : ∀ a, C a) (g : ∀ b, D b) :=
  ∀ a b (r : R a b), S a b r (f a) (g b)

/-- Applying dependently related functions to related inputs produces related outputs. -/
def DependentRespectful.app {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    {f : ∀ a, C a} {g : ∀ b, D b}
    (hfg : DependentRespectful R S f g) {a : A} {b : B} (r : R a b) :
    S a b r (f a) (g b) :=
  hfg a b r

/-- A pointwise dependent relational proof is the lambda rule for dependent respectful products. -/
def DependentRespectful.lam {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    {f : ∀ a, C a} {g : ∀ b, D b}
    (hfg : ∀ a b (r : R a b), S a b r (f a) (g b)) :
    DependentRespectful R S f g :=
  hfg

/-- Dependent function witnesses weaken contravariantly in their input relation and covariantly in
their output relation. -/
def DependentRespectful.weaken {A : Type u} {B : Type v}
    {R : A → B → Sort w} {R' : A → B → Sort w'}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w}
    {S' : ∀ a b, R' a b → C a → D b → Sort w'}
    (domain : ∀ a b, R' a b → R a b)
    (codomain : ∀ a b (r' : R' a b) c d, S a b (domain a b r') c d → S' a b r' c d)
    {f : ∀ a, C a} {g : ∀ b, D b}
    (hfg : DependentRespectful R S f g) : DependentRespectful R' S' f g :=
  fun a b r' => codomain a b r' _ _ (hfg a b (domain a b r'))

/-- For constant families and witness-independent output relations, the dependent product is the
ordinary respectful arrow. -/
theorem dependentRespectful_const_iff {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    (R : A → B → Prop) (S : C → D → Prop) (f : A → C) (g : B → D) :
    DependentRespectful R (fun _ _ _ => S) f g ↔ Respectful R S f g :=
  Iff.rfl

/-- The dependent sigma relation pairs an input witness with a relatedness witness for the
corresponding dependent components. -/
def DependentSigmaRel {A : Type u} {B : Type v} (R : A → B → Sort w)
    {C : A → Type u'} {D : B → Type v'}
    (S : ∀ a b, R a b → C a → D b → Sort w')
    (x : Sigma C) (y : Sigma D) :=
  PSigma fun r : R x.1 y.1 => S x.1 y.1 r x.2 y.2

/-- Related base and fiber components form related dependent pairs. -/
def DependentSigmaRel.mk {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    {a : A} {b : B} {c : C a} {d : D b} (r : R a b) (s : S a b r c d) :
    DependentSigmaRel R S ⟨a, c⟩ ⟨b, d⟩ :=
  ⟨r, s⟩

/-- `ListRel R xs ys` stores one `R` witness for each pair of corresponding list elements. -/
inductive ListRel {A : Type u} {B : Type v} (R : A → B → Type w) :
    List A → List B → Type (max u v w) where
  /-- Empty lists are related. -/
  | nil : ListRel R [] []
  /-- Related heads and tails form related lists. -/
  | cons {a : A} {b : B} {as : List A} {bs : List B}
      (head : R a b) (tail : ListRel R as bs) : ListRel R (a :: as) (b :: bs)

/-- A pointwise transformation of relation witnesses lifts to list-relation witnesses. -/
def ListRel.mapRelation {A : Type u} {B : Type v} {R : A → B → Type w}
    {S : A → B → Type w'} (h : ∀ a b, R a b → S a b) :
    ∀ {xs ys}, ListRel R xs ys → ListRel S xs ys
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (h _ _ head) (tail.mapRelation h)

/-- Pointwise related functions send related lists to related mapped lists. -/
def ListRel.map {A : Type u} {B : Type v} {C : Type u'} {D : Type v'}
    {R : A → B → Type w} {S : C → D → Type w'}
    {f : A → C} {g : B → D} (hfg : ∀ a b, R a b → S (f a) (g b)) :
    ∀ {xs ys}, ListRel R xs ys → ListRel S (xs.map f) (ys.map g)
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (hfg _ _ head) (tail.map hfg)

example {A : Type u} {B : Type v} {C : A → Type u'} {D : B → Type v'}
    {R : A → B → Prop} {S : ∀ a b, R a b → C a → D b → Prop}
    {f : ∀ a, C a} {g : ∀ b, D b}
    (h : DependentRespectful R S f g) {a b} (r : R a b) : S a b r (f a) (g b) :=
  h.app r

end DeepWiki.Refine
