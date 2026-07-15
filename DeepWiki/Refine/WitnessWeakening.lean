import DeepWiki.Refine.CoreParametricity

/-! # Recursive weakening of relational witnesses

Relation changes lift recursively through function types. The domain is transformed in the reverse
direction and the codomain in the forward direction, matching relational variance. -/

set_option linter.defProp false

namespace DeepWiki.Refine

universe u v

/-- A bidirectional logical change between two relations on the same carriers. -/
structure RelationChange {A : Type u} {B : Type v} (R S : A → B → Prop) where
  /-- Transform an `R` witness into an `S` witness. -/
  forward : ∀ a b, R a b → S a b
  /-- Transform an `S` witness back into an `R` witness. -/
  backward : ∀ a b, S a b → R a b

/-- The identity change of a relation. -/
def RelationChange.refl {A : Type u} {B : Type v} (R : A → B → Prop) : RelationChange R R where
  forward := fun _ _ h => h
  backward := fun _ _ h => h

/-- Reverse a bidirectional relation change. -/
def RelationChange.symm {A : Type u} {B : Type v} {R S : A → B → Prop}
    (change : RelationChange R S) : RelationChange S R where
  forward := change.backward
  backward := change.forward

/-- Recursively transform a relational witness through a core type. Function domains use the
backward transformation and function codomains use the forward transformation. -/
def CoreType.relForward {A : Type u} {B : Type v} {R S : A → B → Prop}
    (change : RelationChange R S) :
    (type : CoreType) → {left : type.interpret A} → {right : type.interpret B} →
      type.rel R left right → type.rel S left right
  | .base, _, _, witness => change.forward _ _ witness
  | .arrow domain codomain, _, _, witness => fun a b related =>
      codomain.relForward change (witness a b (domain.relForward change.symm related))

/-- Recursively transform a relational witness in the reverse direction. -/
def CoreType.relBackward {A : Type u} {B : Type v} {R S : A → B → Prop}
    (change : RelationChange R S) (type : CoreType)
    {left : type.interpret A} {right : type.interpret B}
    (witness : type.rel S left right) : type.rel R left right :=
  type.relForward change.symm witness

/-- Recursive witness transformation is an equivalence for proposition-valued relations. -/
def CoreType.relEquiv {A : Type u} {B : Type v} {R S : A → B → Prop}
    (change : RelationChange R S) (type : CoreType)
    (left : type.interpret A) (right : type.interpret B) :
    type.rel R left right ≃ type.rel S left right where
  toFun := type.relForward change
  invFun := type.relBackward change
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- A recursively weakened interpretation contains both the weakened relation-class record and the
correspondingly transformed term witness. -/
structure WeakenedInterpretation {A : Type u} {B : Type v} (R : A → B → Prop)
    (annotation : Annotation) (type : CoreType)
    (left : type.interpret A) (right : type.interpret B) where
  /-- Relation structure retained at the requested lower annotation. -/
  relationClass : RelationClass annotation R
  /-- The relational interpretation of the terms at the core type. -/
  witness : type.rel R left right

/-- Simultaneously forget relation-class fields and recursively weaken the associated witness. -/
def WeakenedInterpretation.ofHigher {A : Type u} {B : Type v} {R : A → B → Prop}
    {low high : Annotation} (annotationLe : low ≤ high)
    (relationClass : RelationClass high R) (type : CoreType)
    {left : type.interpret A} {right : type.interpret B}
    (witness : type.rel R left right) :
    WeakenedInterpretation R low type left right where
  relationClass := relationClass.weaken annotationLe
  witness := type.relForward (RelationChange.refl R) witness

/-- Recursive identity weakening preserves proposition-valued witnesses. -/
theorem CoreType.relForward_refl {A : Type u} {B : Type v} {R : A → B → Prop}
    (type : CoreType) {left : type.interpret A} {right : type.interpret B}
    (witness : type.rel R left right) :
    type.relForward (RelationChange.refl R) witness = witness :=
  Subsingleton.elim _ _

example {A : Type u} {B : Type v} {R S : A → B → Prop}
    (change : RelationChange R S) {domain codomain : CoreType}
    {f : (CoreType.arrow domain codomain).interpret A}
    {g : (CoreType.arrow domain codomain).interpret B}
    (witness : (CoreType.arrow domain codomain).rel R f g) :
    (CoreType.arrow domain codomain).rel S f g :=
  (CoreType.arrow domain codomain).relForward change witness

end DeepWiki.Refine
