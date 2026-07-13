import DeepWiki.Refine.CoreParametricity
import DeepWiki.Refine.TypeEquivalence

/-! # Raw and univalent parametricity translations

Raw parametricity interprets universes by arbitrary heterogeneous relations and dependent products
by dependent respectful functions. Univalent parametricity refines a universe relation with an
equivalence and a pointwise identification with its equality graph. -/

namespace DeepWiki.Refine

universe u v w u' v' w'

noncomputable section

/-- A raw universe interpretation is an arbitrary proof-relevant heterogeneous relation. -/
abbrev RawUniverseRelation (A : Type u) (B : Type v) := A → B → Type w

/-- The raw translation of a universe is itself a relation between types in the next universe. -/
def rawUniverseTranslation : RawUniverseRelation (Type u) (Type u) :=
  fun A B => A → B → Type u

/-- Applying the raw universe translation returns the type of heterogeneous relations. -/
theorem rawUniverseTranslation_apply (A B : Type u) :
    rawUniverseTranslation A B = (A → B → Type u) :=
  rfl

/-- The raw interpretation of a dependent product is the dependent respectful relation. -/
abbrev RawPiRelation {A : Type u} {B : Type v} (R : A → B → Sort w)
    {C : A → Type u'} {D : B → Type v'}
    (S : ∀ a b, R a b → C a → D b → Sort w') :=
  DependentRespectful R S

/-- Raw application applies a related function to related arguments. -/
def RawPiRelation.app {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    {f : ∀ a, C a} {g : ∀ b, D b}
    (functionWitness : RawPiRelation R S f g) {a : A} {b : B} (argumentWitness : R a b) :
    S a b argumentWitness (f a) (g b) :=
  functionWitness a b argumentWitness

/-- Raw lambda translation turns a pointwise relational term into a related dependent function. -/
def RawPiRelation.lam {A : Type u} {B : Type v} {R : A → B → Sort w}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    {f : ∀ a, C a} {g : ∀ b, D b}
    (bodyWitness : ∀ a b (r : R a b), S a b r (f a) (g b)) :
    RawPiRelation R S f g :=
  bodyWitness

/-- Proof-relevant relational interpretation of the intrinsic core types. -/
def CoreType.proofRelevantRel {A B : Type u} (R : A → B → Type u) :
    (type : CoreType) → type.interpret A → type.interpret B → Type u
  | .base => R
  | .arrow domain codomain => fun f g =>
      ∀ a b, domain.proofRelevantRel R a b → codomain.proofRelevantRel R (f a) (g b)

/-- Proof-relevant relation environments implement the raw context-extension rule. -/
inductive CoreEnv.ProofRelevantRel {A B : Type u} (R : A → B → Type u) :
    {context : List CoreType} → CoreEnv A context → CoreEnv B context → Type u where
  /-- The two empty environments are related. -/
  | nil : CoreEnv.ProofRelevantRel R .nil .nil
  /-- A relation witness extends two already-related environments. -/
  | cons : CoreType.proofRelevantRel R type left right →
      CoreEnv.ProofRelevantRel R leftEnv rightEnv →
      CoreEnv.ProofRelevantRel R (.cons left leftEnv) (.cons right rightEnv)

/-- A proof-relevant relation environment contains the translated witness for every variable. -/
noncomputable def CoreEnv.ProofRelevantRel.get
    {A B : Type u} {R : A → B → Type u}
    (var : CoreVar context type) {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context}
    (contextWitness : CoreEnv.ProofRelevantRel R leftEnv rightEnv) :
    CoreType.proofRelevantRel R type (leftEnv.get var) (rightEnv.get var) := by
  induction var with
  | zero => cases contextWitness with | cons head _ => exact head
  | succ var ih => cases contextWitness with | cons _ tail => exact ih tail

/-- Proof-relevant abstraction witness for the intrinsic core calculus. -/
noncomputable def CoreTerm.proofRelevantAbstraction
    {A B : Type u} {R : A → B → Type u}
    (term : CoreTerm context type) {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context}
    (contextWitness : CoreEnv.ProofRelevantRel R leftEnv rightEnv) :
    CoreType.proofRelevantRel R type (term.evaluate leftEnv) (term.evaluate rightEnv) := by
  induction term with
  | var x => exact contextWitness.get x
  | app fn arg ihFn ihArg => exact ihFn contextWitness _ _ (ihArg contextWitness)
  | lam body ih =>
      intro left right related
      exact ih (.cons related contextWitness)

/-- The three outputs of raw abstraction: two typed interpretations and their relation witness. -/
structure CoreTerm.RawAbstractionResult {A B : Type u} (R : A → B → Type u)
    (type : CoreType) where
  /-- Interpretation of the original term. -/
  original : type.interpret A
  /-- Interpretation of the primed term. -/
  primed : type.interpret B
  /-- The translated term relating the original and primed interpretations. -/
  translated : type.proofRelevantRel R original primed

/-- Raw abstraction packages both interpretations and the structurally generated relation witness. -/
noncomputable def CoreTerm.rawAbstractionResult
    {A B : Type u} {R : A → B → Type u}
    (term : CoreTerm context type) (leftEnv : CoreEnv A context) (rightEnv : CoreEnv B context)
    (contextWitness : CoreEnv.ProofRelevantRel R leftEnv rightEnv) :
    CoreTerm.RawAbstractionResult R type where
  original := term.evaluate leftEnv
  primed := term.evaluate rightEnv
  translated := term.proofRelevantAbstraction contextWitness

/-- The equality graph of backward transport, lifted into the carrier universe. -/
abbrev BackwardEqualityGraph {A B : Type u} (equivalence : A ≃ B) (a : A) (b : B) :=
  ULift.{u} (PLift (a = equivalence.symm b))

/-- A univalent universe relation packages a relation, an equivalence, and identification of the
relation with the equality graph of backward transport. -/
structure UnivalentRelation (A B : Type u) where
  /-- The type equivalence carried by the universe relation. -/
  equivalence : A ≃ B
  /-- The proof-relevant heterogeneous relation between elements. -/
  relation : A → B → Type u
  /-- Each relation fiber is equivalent to equality after backward transport. -/
  relationEquiv : ∀ a b, relation a b ≃ BackwardEqualityGraph equivalence a b

/-- Two univalent relation packages agree when their equivalences and relation families agree. -/
@[ext] theorem UnivalentRelation.ext {A B : Type u} {left right : UnivalentRelation A B}
    (equivalence_eq : left.equivalence = right.equivalence)
    (relation_eq : left.relation = right.relation) : left = right := by
  cases left with
  | mk leftEquivalence leftRelation leftRelationEquiv =>
    cases right with
    | mk rightEquivalence rightRelation rightRelationEquiv =>
      cases equivalence_eq
      cases relation_eq
      congr
      funext a b
      apply Equiv.ext
      intro witness
      exact Subsingleton.elim _ _

/-- The relation used in a translated typing judgment is the first relational projection of the
univalent universe package. -/
def UnivalentRelation.rel {A B : Type u} (package : UnivalentRelation A B) :
    A → B → Type u :=
  package.relation

/-- Every type equivalence has a canonical univalent relation given by its equality graph. -/
def UnivalentRelation.ofEquiv {A B : Type u} (equivalence : A ≃ B) :
    UnivalentRelation A B where
  equivalence := equivalence
  relation := BackwardEqualityGraph equivalence
  relationEquiv := fun _ _ => Equiv.refl _

/-- Univalence identifies the relation family in a universe package with its equality graph. -/
theorem UnivalentRelation.relation_eq_graph (univalent : IsUnivalentUniverse.{u})
    {A B : Type u} (package : UnivalentRelation A B) :
    package.relation = BackwardEqualityGraph package.equivalence := by
  funext a b
  exact univalent.pathOfEquivalence (package.relationEquiv a b)

/-- Assuming univalence, universe-relation packages are equivalent to ordinary type equivalences. -/
def univalentRelationEquivTypeEquivalence (univalent : IsUnivalentUniverse.{u})
    (A B : Type u) : UnivalentRelation A B ≃ (A ≃ B) where
  toFun := UnivalentRelation.equivalence
  invFun := UnivalentRelation.ofEquiv
  left_inv := fun package => by
    apply UnivalentRelation.ext
    · apply Equiv.ext
      intro a
      rfl
    · exact (package.relation_eq_graph univalent).symm
  right_inv := fun _ => by
    apply Equiv.ext
    intro a
    rfl

/-- Under univalence, the translated universe is itself a well-formed univalent relation package. -/
def univalentUniverseRelation (univalent : IsUnivalentUniverse.{u}) :
    UnivalentRelation (Type u) (Type u) where
  equivalence := Equiv.refl (Type u)
  relation := UnivalentRelation
  relationEquiv := fun A B =>
    (univalentRelationEquivTypeEquivalence univalent A B).trans
      ((univalent A B).toEquiv.symm.trans
        (Equiv.plift.symm.trans Equiv.ulift.symm))

/-- Projecting the translated universe package recovers the univalent relation interpretation. -/
theorem univalentUniverseRelation_rel (univalent : IsUnivalentUniverse.{u}) :
    (univalentUniverseRelation univalent).rel = UnivalentRelation :=
  rfl

/-- Raw abstraction theorem for the proof-relevant intrinsic lambda fragment. -/
theorem CoreTerm.rawParametricity {A : Type u} {B : Type v} {R : A → B → Prop}
    (term : CoreTerm context type) {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context}
    (contextWitness : CoreEnv.Rel R leftEnv rightEnv) :
    CoreType.rel R type (term.evaluate leftEnv) (term.evaluate rightEnv) :=
  term.abstraction contextWitness

/-- Univalent abstraction theorem for the intrinsic fragment, obtained by restricting the raw
translation to the relation projected from a univalent universe package. -/
noncomputable def CoreTerm.univalentParametricity
    {A B : Type u} (package : UnivalentRelation A B)
    (term : CoreTerm context type) {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context}
    (contextWitness : CoreEnv.ProofRelevantRel package.rel leftEnv rightEnv) :
    CoreType.proofRelevantRel package.rel type (term.evaluate leftEnv) (term.evaluate rightEnv) :=
  term.proofRelevantAbstraction contextWitness

/-- Univalent abstraction packages both term copies and their projected univalent witness. -/
noncomputable def CoreTerm.univalentAbstractionResult
    {A B : Type u} (package : UnivalentRelation A B)
    (term : CoreTerm context type) (leftEnv : CoreEnv A context) (rightEnv : CoreEnv B context)
    (contextWitness : CoreEnv.ProofRelevantRel package.rel leftEnv rightEnv) :
    CoreTerm.RawAbstractionResult package.rel type :=
  term.rawAbstractionResult leftEnv rightEnv contextWitness

example {A : Type u} {B : Type v} {R : A → B → Prop}
    {C : A → Type u'} {D : B → Type v'}
    {S : ∀ a b, R a b → C a → D b → Sort w'}
    {f : ∀ a, C a} {g : ∀ b, D b}
    (functionWitness : RawPiRelation R S f g) {a b} (argumentWitness : R a b) :
    S a b argumentWitness (f a) (g b) :=
  functionWitness.app argumentWitness

example (univalent : IsUnivalentUniverse.{u}) (A B : Type u) :
    UnivalentRelation A B ≃ (A ≃ B) :=
  univalentRelationEquivTypeEquivalence univalent A B

example (univalent : IsUnivalentUniverse.{u}) :
    (univalentUniverseRelation univalent).rel = UnivalentRelation :=
  univalentUniverseRelation_rel univalent

example (A B : Type u) : rawUniverseTranslation A B = (A → B → Type u) :=
  rawUniverseTranslation_apply A B

example {A : Type u} {B : Type v} {R : A → B → Prop}
    (term : CoreTerm context type) {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context}
    (contextWitness : CoreEnv.Rel R leftEnv rightEnv) :
    CoreType.rel R type (term.evaluate leftEnv) (term.evaluate rightEnv) :=
  term.rawParametricity contextWitness

example {A B : Type u} (package : UnivalentRelation A B)
    (term : CoreTerm context type) {leftEnv : CoreEnv A context} {rightEnv : CoreEnv B context}
    (contextWitness : CoreEnv.ProofRelevantRel package.rel leftEnv rightEnv) :
    CoreType.proofRelevantRel package.rel type (term.evaluate leftEnv) (term.evaluate rightEnv) :=
  term.univalentParametricity package contextWitness

example {A B : Type u} {R : A → B → Type u}
    (term : CoreTerm context type) (leftEnv : CoreEnv A context) (rightEnv : CoreEnv B context)
    (contextWitness : CoreEnv.ProofRelevantRel R leftEnv rightEnv) :
    CoreTerm.RawAbstractionResult R type :=
  term.rawAbstractionResult leftEnv rightEnv contextWitness

end

end DeepWiki.Refine
