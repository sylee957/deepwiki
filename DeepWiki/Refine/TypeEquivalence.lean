import Mathlib.Logic.Equiv.Defs

/-! # Type equivalence and univalent transport

Two-sided inverses yield coherent equivalences because Lean's equality proofs are proof-irrelevant.
Universe univalence is represented as additional data, without assuming it as an axiom. -/

set_option linter.defProp false

namespace DeepWiki.Refine

universe u v w x

/-- Two functions are pointwise equal when they agree on every argument. -/
def PointwiseEq {A : Sort u} {B : Sort v} (f g : A → B) : Prop :=
  ∀ a, f a = g a

/-- Pointwise equality of functions is equivalent to ordinary function equality. -/
theorem pointwiseEq_iff_eq {A : Sort u} {B : Sort v} {f g : A → B} :
    PointwiseEq f g ↔ f = g :=
  ⟨fun h => funext h, fun h a => congrFun h a⟩

/-- Isomorphism data for a function consists of an inverse satisfying the two triangle laws. -/
structure IsomorphismData {A : Sort u} {B : Sort v} (f : A → B) where
  /-- The inverse map. -/
  inverse : B → A
  /-- Applying the inverse after the map is pointwise the identity. -/
  sectionLaw : ∀ a, inverse (f a) = a
  /-- Applying the map after the inverse is pointwise the identity. -/
  retractionLaw : ∀ b, f (inverse b) = b

/-- Two isomorphism packages for the same function agree when their inverse maps agree. -/
@[ext] theorem IsomorphismData.ext {A : Sort u} {B : Sort v} {f : A → B}
    {left right : IsomorphismData f} (inverse_eq : left.inverse = right.inverse) : left = right := by
  cases left
  cases right
  cases inverse_eq
  rfl

/-- In Lean, two-sided inverse data for a fixed function is proof-irrelevant. -/
theorem isomorphismData_subsingleton {A : Sort u} {B : Sort v} (f : A → B) :
    Subsingleton (IsomorphismData f) := by
  constructor
  intro left right
  apply IsomorphismData.ext
  funext b
  calc
    left.inverse b = left.inverse (f (right.inverse b)) :=
      congrArg left.inverse (right.retractionLaw b).symm
    _ = right.inverse b := left.sectionLaw (right.inverse b)

/-- Coherent equivalence data additionally identifies the two induced proofs over each image. -/
structure CoherentEquivalenceData {A : Sort u} {B : Sort v} (f : A → B)
    extends IsomorphismData f where
  /-- The section transported through `f` agrees with the retraction over `f a`. -/
  coherence : ∀ a, congrArg f (toIsomorphismData.sectionLaw a) =
    toIsomorphismData.retractionLaw (f a)

/-- Coherent equivalence packages agree when their underlying isomorphism data agrees. -/
@[ext] theorem CoherentEquivalenceData.ext {A : Sort u} {B : Sort v} {f : A → B}
    {left right : CoherentEquivalenceData f}
    (data_eq : left.toIsomorphismData = right.toIsomorphismData) : left = right := by
  cases left
  cases right
  cases data_eq
  rfl

/-- Coherent equivalence evidence for a fixed function is proof-irrelevant. -/
theorem coherentEquivalenceData_subsingleton {A : Sort u} {B : Sort v} (f : A → B) :
    Subsingleton (CoherentEquivalenceData f) := by
  constructor
  intro left right
  apply CoherentEquivalenceData.ext
  exact (isomorphismData_subsingleton f).elim _ _

/-- In Lean, any two-sided isomorphism is coherently equivalent by proof irrelevance. -/
def IsomorphismData.toCoherentEquivalence {A : Sort u} {B : Sort v} {f : A → B}
    (isomorphism : IsomorphismData f) : CoherentEquivalenceData f where
  toIsomorphismData := isomorphism
  coherence := fun _ => Subsingleton.elim _ _

/-- Coherent equivalence data determines a standard Lean equivalence. -/
def CoherentEquivalenceData.toEquiv {A : Sort u} {B : Sort v} {f : A → B}
    (equivalence : CoherentEquivalenceData f) : A ≃ B where
  toFun := f
  invFun := equivalence.inverse
  left_inv := equivalence.sectionLaw
  right_inv := equivalence.retractionLaw

/-- A type equivalence can be presented as a map paired with coherent equivalence evidence. -/
abbrev TypeEquivalenceData (A : Type u) (B : Type v) :=
  Σ f : A → B, CoherentEquivalenceData f

/-- The dependent-pair presentation of type equivalence determines a standard Lean equivalence. -/
def TypeEquivalenceData.toEquiv {A : Type u} {B : Type v}
    (equivalence : TypeEquivalenceData A B) : A ≃ B :=
  equivalence.2.toEquiv

/-- A standard Lean equivalence supplies two-sided isomorphism data for its forward map. -/
def Equiv.toIsomorphismData {A : Sort u} {B : Sort v} (equivalence : A ≃ B) :
    IsomorphismData equivalence where
  inverse := equivalence.symm
  sectionLaw := equivalence.left_inv
  retractionLaw := equivalence.right_inv

/-- A standard Lean equivalence supplies dependent-pair equivalence data. -/
def TypeEquivalenceData.ofEquiv {A : Type u} {B : Type v} (equivalence : A ≃ B) :
    TypeEquivalenceData A B :=
  ⟨equivalence, (Equiv.toIsomorphismData equivalence).toCoherentEquivalence⟩

/-- Converting dependent-pair equivalence data to Lean and back recovers the original data. -/
theorem TypeEquivalenceData.toEquiv_ofEquiv {A : Type u} {B : Type v}
    (equivalence : TypeEquivalenceData A B) :
    TypeEquivalenceData.ofEquiv equivalence.toEquiv = equivalence := by
  rcases equivalence with ⟨f, evidence⟩
  let hfun : (TypeEquivalenceData.ofEquiv evidence.toEquiv).1 = f := by
    funext a
    rfl
  apply Sigma.ext hfun
  cases hfun
  exact heq_of_eq ((coherentEquivalenceData_subsingleton f).elim _ _)

/-- Converting a Lean equivalence to dependent-pair data and back recovers the equivalence. -/
theorem TypeEquivalenceData.ofEquiv_toEquiv {A : Type u} {B : Type v}
    (equivalence : A ≃ B) :
    (TypeEquivalenceData.ofEquiv equivalence).toEquiv = equivalence := by
  apply Equiv.ext
  intro a
  change equivalence a = equivalence a
  rfl

/-- The dependent-pair presentation of type equivalence is equivalent to Lean's bundled `Equiv`. -/
def typeEquivalenceDataEquivEquiv (A : Type u) (B : Type v) :
    TypeEquivalenceData A B ≃ (A ≃ B) where
  toFun := TypeEquivalenceData.toEquiv
  invFun := TypeEquivalenceData.ofEquiv
  left_inv := TypeEquivalenceData.toEquiv_ofEquiv
  right_inv := TypeEquivalenceData.ofEquiv_toEquiv

/-- The section and retraction proofs of a Lean equivalence satisfy the coherence equation. -/
theorem Equiv.coherence {A : Sort u} {B : Sort v} (equivalence : A ≃ B) (a : A) :
    congrArg equivalence (equivalence.left_inv a) = equivalence.right_inv (equivalence a) :=
  Subsingleton.elim _ _

/-- Type equivalence is represented by Lean's standard bundled equivalence. -/
abbrev TypeEquivalence (A : Type u) (B : Type v) := A ≃ B

/-- The forward transport function carried by a type equivalence. -/
def TypeEquivalence.forward {A : Type u} {B : Type v} (equivalence : TypeEquivalence A B) :
    A → B :=
  equivalence

/-- The backward transport function carried by a type equivalence. -/
def TypeEquivalence.backward {A : Type u} {B : Type v} (equivalence : TypeEquivalence A B) :
    B → A :=
  equivalence.symm

/-- Arrow equivalence uses backward transport in the domain and forward transport in the codomain. -/
def TypeEquivalence.arrow {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    (domain : TypeEquivalence A B) (codomain : TypeEquivalence C D) :
    TypeEquivalence (A → C) (B → D) where
  toFun f b := codomain (f (domain.symm b))
  invFun g a := codomain.symm (g (domain a))
  left_inv f := by
    funext a
    simp
  right_inv g := by
    funext b
    simp

/-- Equality of types canonically induces an equivalence of types. -/
def eqToTypeEquivalence {A B : Type u} (path : A = B) : TypeEquivalence A B := by
  cases path
  exact Equiv.refl A

/-- A universe is univalent when equality-to-equivalence carries coherent equivalence evidence. -/
def IsUnivalentUniverse : Type (u + 1) :=
  ∀ A B : Type u, CoherentEquivalenceData (fun path : A = B => eqToTypeEquivalence path)

/-- Univalence evidence for a fixed Lean universe is proof-irrelevant. -/
theorem isUnivalentUniverse_subsingleton : Subsingleton IsUnivalentUniverse.{u} := by
  constructor
  intro left right
  funext A B
  exact (coherentEquivalenceData_subsingleton
    (fun path : A = B => eqToTypeEquivalence path)).elim _ _

/-- Univalence converts an equivalence of types back into an equality of types. -/
def IsUnivalentUniverse.pathOfEquivalence (univalent : IsUnivalentUniverse.{u})
    {A B : Type u} (equivalence : TypeEquivalence A B) : A = B :=
  (univalent A B).inverse equivalence

/-- Re-encoding the equality supplied by univalence recovers the original equivalence. -/
theorem IsUnivalentUniverse.eqTo_pathOfEquivalence (univalent : IsUnivalentUniverse.{u})
    {A B : Type u} (equivalence : TypeEquivalence A B) :
    eqToTypeEquivalence (univalent.pathOfEquivalence equivalence) = equivalence :=
  (univalent A B).retractionLaw equivalence

/-- Applying univalence to a canonical equality equivalence recovers the original equality. -/
theorem IsUnivalentUniverse.pathOfEquivalence_eqTo (univalent : IsUnivalentUniverse.{u})
    {A B : Type u} (path : A = B) :
    univalent.pathOfEquivalence (eqToTypeEquivalence path) = path :=
  (univalent A B).sectionLaw path

/-- Proof-irrelevant equality makes univalence evidence for a standard Lean universe empty. -/
theorem isEmpty_isUnivalentUniverse : IsEmpty IsUnivalentUniverse.{u} := by
  constructor
  intro univalent
  let Carrier : Type u := ULift.{u} Bool
  let identity : Carrier ≃ Carrier := Equiv.refl Carrier
  let negation : Carrier ≃ Carrier :=
    { toFun := fun value => ⟨Bool.not value.down⟩
      invFun := fun value => ⟨Bool.not value.down⟩
      left_inv := fun value => by rcases value with ⟨value⟩; cases value <;> rfl
      right_inv := fun value => by rcases value with ⟨value⟩; cases value <;> rfl }
  let identityPath : Carrier = Carrier := univalent.pathOfEquivalence identity
  let negationPath : Carrier = Carrier := univalent.pathOfEquivalence negation
  have pathsEqual : identityPath = negationPath := Subsingleton.elim _ _
  have equivalencesEqual : identity = negation := by
    calc
      identity = eqToTypeEquivalence identityPath :=
        (univalent.eqTo_pathOfEquivalence identity).symm
      _ = eqToTypeEquivalence negationPath :=
        congrArg (fun path : Carrier = Carrier => eqToTypeEquivalence path) pathsEqual
      _ = negation := univalent.eqTo_pathOfEquivalence negation
  have liftedFalse_eq_liftedTrue :
      (ULift.up false : Carrier) = ULift.up true := by
    exact congrArg
      (fun equivalence : Carrier ≃ Carrier => equivalence (ULift.up false))
      equivalencesEqual
  have false_eq_true : false = true := congrArg ULift.down liftedFalse_eq_liftedTrue
  cases false_eq_true

/-- Under univalence, every type former maps equivalent inputs to equivalent output types. -/
def IsUnivalentUniverse.mapTypeFormer (univalent : IsUnivalentUniverse.{u})
    (typeFormer : Type u → Type v) {A B : Type u} (equivalence : TypeEquivalence A B) :
    TypeEquivalence (typeFormer A) (typeFormer B) :=
  eqToTypeEquivalence (congrArg typeFormer (univalent.pathOfEquivalence equivalence))

/-- Under univalence, a proof about one type transports along any equivalence of input types. -/
def IsUnivalentUniverse.transportProof (univalent : IsUnivalentUniverse.{u})
    (motive : Type u → Sort w) {A B : Type u} (equivalence : TypeEquivalence A B)
    (proof : motive A) : motive B :=
  Eq.mp (congrArg motive (univalent.pathOfEquivalence equivalence)) proof

example {A : Type u} {B : Type v} {f : A → B} (isomorphism : IsomorphismData f) :
    CoherentEquivalenceData f :=
  isomorphism.toCoherentEquivalence

example {A : Sort u} {B : Sort v} {f g : A → B} : PointwiseEq f g ↔ f = g :=
  pointwiseEq_iff_eq

example {A : Sort u} {B : Sort v} {f : A → B} : Subsingleton (IsomorphismData f) :=
  isomorphismData_subsingleton f

example {A : Sort u} {B : Sort v} {f : A → B} :
    Subsingleton (CoherentEquivalenceData f) :=
  coherentEquivalenceData_subsingleton f

example (A : Type u) (B : Type v) : TypeEquivalenceData A B ≃ (A ≃ B) :=
  typeEquivalenceDataEquivEquiv A B

example {A : Type u} {B : Type v} (equivalence : TypeEquivalenceData A B) :
    TypeEquivalenceData.ofEquiv equivalence.toEquiv = equivalence :=
  equivalence.toEquiv_ofEquiv

example {A : Type u} {B : Type v} (equivalence : A ≃ B) :
    (TypeEquivalenceData.ofEquiv equivalence).toEquiv = equivalence :=
  TypeEquivalenceData.ofEquiv_toEquiv equivalence

example {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    (domain : A ≃ B) (codomain : C ≃ D) : (A → C) ≃ (B → D) :=
  TypeEquivalence.arrow domain codomain

example : Subsingleton IsUnivalentUniverse.{u} :=
  isUnivalentUniverse_subsingleton

example {A B : Type u} (univalent : IsUnivalentUniverse.{u}) (equivalence : A ≃ B) :
    eqToTypeEquivalence (univalent.pathOfEquivalence equivalence) = equivalence :=
  univalent.eqTo_pathOfEquivalence equivalence

example {A B : Type u} (univalent : IsUnivalentUniverse.{u}) (path : A = B) :
    univalent.pathOfEquivalence (eqToTypeEquivalence path) = path :=
  univalent.pathOfEquivalence_eqTo path

example : IsEmpty IsUnivalentUniverse.{u} :=
  isEmpty_isUnivalentUniverse

example {A B : Type u} (univalent : IsUnivalentUniverse.{u}) (equivalence : A ≃ B)
    (typeFormer : Type u → Type v) : typeFormer A ≃ typeFormer B :=
  univalent.mapTypeFormer typeFormer equivalence

example {A B : Type u} (univalent : IsUnivalentUniverse.{u}) (equivalence : A ≃ B)
    (motive : Type u → Prop) (proof : motive A) : motive B :=
  univalent.transportProof motive equivalence proof

end DeepWiki.Refine
