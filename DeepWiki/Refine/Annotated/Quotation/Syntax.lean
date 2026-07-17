import DeepWiki.Refine.AnnotatedRelationTranslation
import DeepWiki.Refine.UniverseRelationStructure

/-! # Syntax for structured-universe quotation

An intrinsically scoped extension of annotated terms adds structured-relation families,
universe witnesses, and a genuine relation-field projection with computational reduction.
-/

namespace DeepWiki.Refine.StructuredUniverseQuotationSyntax

/-- Terms of the core annotated dependent calculus. -/
abbrev CoreTerm := AnnotatedDependentCalculus.Term

/-- Contexts of the core annotated dependent calculus. -/
abbrev Context := AnnotatedDependentCalculus.Context

/-- Renamings between intrinsically scoped quotation terms. -/
abbrev Renaming := DependentCalculus.Renaming

/-- Annotated terms extended by structured-relation quotation primitives. -/
inductive Term : Nat → Type where
  /-- An annotated universe of the core calculus. -/
  | sort {n : Nat} (level : Nat) (annotation : Annotation) : Term n
  /-- An intrinsically scoped de Bruijn variable. -/
  | var {n : Nat} (index : Fin n) : Term n
  /-- Application of one extended term to another. -/
  | app {n : Nat} (function argument : Term n) : Term n
  /-- A lambda abstraction with an explicit domain. -/
  | lam {n : Nat} (domain : Term n) (body : Term (n + 1)) : Term n
  /-- A dependent product with one bound variable in its codomain. -/
  | pi {n : Nat} (domain : Term n) (codomain : Term (n + 1)) : Term n
  /-- The object-language type of binary relations between two quoted endpoint types. -/
  | relationType {n : Nat} (left right : Term n) : Term n
  /-- The annotation-indexed structured-relation family `Param`. -/
  | relationFamily {n : Nat} (annotation : Annotation) (level : Nat) : Term n
  /-- The structured witness relating two copies of an annotated universe. -/
  | universeWitness {n : Nat} (source target : Annotation) (level : Nat) : Term n
  /-- Projection of the binary-relation field from a structured witness. -/
  | relationProjection {n : Nat} (witness : Term n) : Term n
  deriving DecidableEq, Repr

namespace Term

/-- Rename every free variable, lifting the renaming below binders. -/
def rename (mapping : Renaming source target) : Term source → Term target
  | .sort level annotation => .sort level annotation
  | .var index => .var (mapping index)
  | .app function argument => .app (rename mapping function) (rename mapping argument)
  | .lam domain body =>
      .lam (rename mapping domain)
        (rename (DependentCalculus.Renaming.lift mapping) body)
  | .pi domain codomain =>
      .pi (rename mapping domain)
        (rename (DependentCalculus.Renaming.lift mapping) codomain)
  | .relationType left right => .relationType (rename mapping left) (rename mapping right)
  | .relationFamily annotation level => .relationFamily annotation level
  | .universeWitness source target level => .universeWitness source target level
  | .relationProjection witness => .relationProjection (rename mapping witness)

/-- Weaken an extended term by any number of fresh variables. -/
def weakenBy (term : Term n) : (amount : Nat) → Term (n + amount)
  | 0 => term
  | amount + 1 => (weakenBy term amount).rename DependentCalculus.Renaming.shift

/-- Embed every core annotated term into the quotation syntax. -/
def ofCore : CoreTerm n → Term n
  | .sort level annotation => .sort level annotation
  | .var index => .var index
  | .app function argument => .app (ofCore function) (ofCore argument)
  | .lam domain body => .lam (ofCore domain) (ofCore body)
  | .pi domain codomain => .pi (ofCore domain) (ofCore codomain)

/-- Partially recognize the image of the core-term embedding. -/
def toCore? : Term n → Option (CoreTerm n)
  | .sort level annotation => some (.sort level annotation)
  | .var index => some (.var index)
  | .app function argument =>
      match function.toCore?, argument.toCore? with
      | some coreFunction, some coreArgument => some (.app coreFunction coreArgument)
      | _, _ => none
  | .lam domain body =>
      match domain.toCore?, body.toCore? with
      | some coreDomain, some coreBody => some (.lam coreDomain coreBody)
      | _, _ => none
  | .pi domain codomain =>
      match domain.toCore?, codomain.toCore? with
      | some coreDomain, some coreCodomain => some (.pi coreDomain coreCodomain)
      | _, _ => none
  | .relationType _ _ => none
  | .relationFamily _ _ => none
  | .universeWitness _ _ _ => none
  | .relationProjection _ => none

/-- Recognizing an embedded core term recovers that term exactly. -/
@[simp] theorem toCore?_ofCore (term : CoreTerm n) : toCore? (ofCore term) = some term := by
  induction term with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [ofCore, toCore?, functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [ofCore, toCore?, domainInduction, bodyInduction]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [ofCore, toCore?, domainInduction, codomainInduction]

/-- The embedding of core annotated terms is injective. -/
theorem ofCore_injective : Function.Injective (@ofCore n) := by
  intro left right equal
  have recognized := congrArg toCore? equal
  simpa only [toCore?_ofCore, Option.some.injEq] using recognized

/-- Embedding a renamed core term agrees with renaming its embedding. -/
@[simp] theorem ofCore_rename (term : CoreTerm source)
    (mapping : Renaming source target) :
    ofCore (term.rename mapping) = rename mapping (ofCore term) := by
  induction term generalizing target with
  | sort => rfl
  | var => rfl
  | app function argument functionInduction argumentInduction =>
      simp only [AnnotatedDependentCalculus.Term.rename, ofCore, rename,
        functionInduction, argumentInduction]
  | lam domain body domainInduction bodyInduction =>
      simp only [AnnotatedDependentCalculus.Term.rename, ofCore, rename,
        domainInduction, bodyInduction]
  | pi domain codomain domainInduction codomainInduction =>
      simp only [AnnotatedDependentCalculus.Term.rename, ofCore, rename,
        domainInduction, codomainInduction]

/-- A substitution replaces every source variable by an extended target term. -/
abbrev Substitution (source target : Nat) := Fin source → Term target

namespace Substitution

/-- Lift an extended substitution below one binder. -/
def lift (substitute : Substitution source target) :
    Substitution (source + 1) (target + 1) :=
  Fin.cases (.var 0)
    (fun index => (substitute index).rename DependentCalculus.Renaming.shift)

end Substitution

/-- Perform capture-avoiding simultaneous substitution on an extended term. -/
def substitute (mapping : Substitution source target) : Term source → Term target
  | .sort level annotation => .sort level annotation
  | .var index => mapping index
  | .app function argument =>
      .app (substitute mapping function) (substitute mapping argument)
  | .lam domain body =>
      .lam (substitute mapping domain) (substitute (Substitution.lift mapping) body)
  | .pi domain codomain =>
      .pi (substitute mapping domain) (substitute (Substitution.lift mapping) codomain)
  | .relationType left right =>
      .relationType (substitute mapping left) (substitute mapping right)
  | .relationFamily annotation level => .relationFamily annotation level
  | .universeWitness source target level => .universeWitness source target level
  | .relationProjection witness => .relationProjection (substitute mapping witness)

/-- Substitute one extended term for the newest variable. -/
def instantiate (body : Term (n + 1)) (argument : Term n) : Term n :=
  body.substitute (Fin.cases argument Term.var)

/-- Contract the distinguished structured-universe projection at the head of a term. -/
def contractProjection : Term n → Term n
  | .relationProjection (.universeWitness source _ level) =>
      .relationFamily source level
  | term => term

/-- Projection of a structured universe witness computes to its source relation family. -/
@[simp] theorem contractProjection_universeWitness
    (source target : Annotation) (level : Nat) :
    contractProjection
        (.relationProjection (.universeWitness source target level) : Term n) =
      .relationFamily source level :=
  rfl

/-- Quotation primitives are closed and therefore invariant under renaming. -/
@[simp] theorem rename_relationFamily (mapping : Renaming source target)
    (annotation : Annotation) (level : Nat) :
    rename mapping (.relationFamily annotation level) = .relationFamily annotation level :=
  rfl

/-- Structured universe witnesses are closed and invariant under renaming. -/
@[simp] theorem rename_universeWitness (mapping : Renaming source target)
    (sourceAnnotation targetAnnotation : Annotation) (level : Nat) :
    rename mapping (.universeWitness sourceAnnotation targetAnnotation level) =
      .universeWitness sourceAnnotation targetAnnotation level :=
  rfl

end Term

/-- The type of the source-annotation relation family at one universe level. -/
def relationFamilyType (source : Annotation) (level : Nat) : Term n :=
  .relationType (.sort level source) (.sort level source)

/-- Apply an annotation-indexed structured-relation family to two endpoint types. -/
def structuredRelationType (target : Annotation) (level : Nat)
    (left right : Term n) : Term n :=
  .app (.app (.relationFamily target (level + 1)) left) right

/-- The structured-relation type assigned to an admissible quoted universe witness. -/
def universeWitnessType (source target : Annotation) (level : Nat) : Term n :=
  structuredRelationType target level (.sort level source) (.sort level source)

/-- Projection of the canonical structured universe witness. -/
def projectedRelation (source target : Annotation) (level : Nat) : Term n :=
  .relationProjection (.universeWitness source target level)

/-- Head contraction computes a projected universe witness to its relation family. -/
@[simp] theorem contractProjection_projectedRelation
    (source target : Annotation) (level : Nat) :
    Term.contractProjection (projectedRelation source target level : Term n) =
      .relationFamily source level :=
  rfl

/-- Application of a quoted binary relation to two endpoints. -/
def relationApplication (relation left right : Term n) : Term n :=
  .app (.app relation left) right

/-- One compatible computational reduction step in the quotation syntax. -/
inductive BetaStep : Term n → Term n → Prop where
  /-- Every core annotated beta step remains a reduction after embedding. -/
  | core {left right : CoreTerm n}
      (step : AnnotatedDependentCalculus.BetaStep left right) :
      BetaStep (Term.ofCore left) (Term.ofCore right)
  /-- Contract an extended lambda application. -/
  | beta (domain : Term n) (body : Term (n + 1)) (argument : Term n) :
      BetaStep (.app (.lam domain body) argument) (body.instantiate argument)
  /-- Projecting the canonical universe witness returns its source relation family. -/
  | universeProjection (source target : Annotation) (level : Nat) :
      BetaStep (projectedRelation source target level) (.relationFamily source level)
  /-- Reduction is compatible with an application's function. -/
  | appFunction {function function' argument : Term n}
      (step : BetaStep function function') :
      BetaStep (.app function argument) (.app function' argument)
  /-- Reduction is compatible with an application's argument. -/
  | appArgument {function argument argument' : Term n}
      (step : BetaStep argument argument') :
      BetaStep (.app function argument) (.app function argument')
  /-- Reduction is compatible with relation-field projection. -/
  | relationProjection {witness witness' : Term n}
      (step : BetaStep witness witness') :
      BetaStep (.relationProjection witness) (.relationProjection witness')

/-- Definitional conversion is the equivalence closure of quotation reduction. -/
inductive Convertible : Term n → Term n → Prop where
  /-- Every quotation term is convertible to itself. -/
  | refl (term : Term n) : Convertible term term
  /-- Every quotation reduction is a definitional conversion. -/
  | beta {left right : Term n} (step : BetaStep left right) : Convertible left right
  /-- Definitional conversion is symmetric. -/
  | symm {left right : Term n} (conversion : Convertible left right) :
      Convertible right left
  /-- Definitional conversion is transitive. -/
  | trans {first second third : Term n}
      (firstSecond : Convertible first second) (secondThird : Convertible second third) :
      Convertible first third

namespace Convertible

/-- Core annotated conversion remains valid after embedding into quotation syntax. -/
theorem ofCore {left right : CoreTerm n}
    (conversion : AnnotatedDependentCalculus.Convertible left right) :
    Convertible (Term.ofCore left) (Term.ofCore right) := by
  induction conversion with
  | refl term => exact .refl (Term.ofCore term)
  | beta step => exact .beta (.core step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Definitional conversion is compatible with application in function position. -/
theorem appFunction {function function' argument : Term n}
    (conversion : Convertible function function') :
    Convertible (.app function argument) (.app function' argument) := by
  induction conversion with
  | refl => exact .refl _
  | beta step => exact .beta (.appFunction step)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

end Convertible

/-- Typing for the core calculus extended by structured-relation quotation rules. -/
inductive HasType : Context n → Term n → Term n → Prop where
  /-- Every core annotated typing derivation remains valid after embedding. -/
  | core {context : Context n} {term type : CoreTerm n}
      (typing : AnnotatedDependentCalculus.HasType context term type) :
      HasType context (Term.ofCore term) (Term.ofCore type)
  /-- Extended dependent application instantiates its codomain. -/
  | app {context : Context n} {function argument domain : Term n}
      {codomain : Term (n + 1)}
      (functionTyping : HasType context function (.pi domain codomain))
      (argumentTyping : HasType context argument domain) :
      HasType context (.app function argument) (codomain.instantiate argument)
  /-- Every quoted relation family has the binary-relation type for its universe. -/
  | relationFamily {context : Context n}
      (contextWellFormed : AnnotatedDependentCalculus.WellFormed context)
      (source : Annotation) (level : Nat) :
      HasType context (.relationFamily source level) (relationFamilyType source level)
  /-- An admissible universe pair supplies the canonical structured witness. -/
  | universeWitness {context : Context n}
      (contextWellFormed : AnnotatedDependentCalculus.WellFormed context)
      {source target : Annotation}
      (admissible : AdmissibleUniverseTranslation source target) (level : Nat) :
      HasType context (.universeWitness source target level)
        (universeWitnessType source target level)
  /-- A structured witness's projected field is a binary relation on its endpoints. -/
  | relationProjection {context : Context n} {witness left right : Term n}
      {target : Annotation} {level : Nat}
      (witnessTyping : HasType context witness
        (structuredRelationType target level left right)) :
      HasType context (.relationProjection witness) (.relationType left right)

/-- The canonical structured-universe witness has exactly its displayed quoted type. -/
theorem universeWitness_hasType {source target : Annotation} {level : Nat}
    (admissible : AdmissibleUniverseTranslation source target) :
    HasType .empty (.universeWitness source target level : Term 0)
      (universeWitnessType source target level) :=
  .universeWitness .empty admissible level

/-- The projected canonical witness has the source relation family's type. -/
theorem projectedRelation_hasType {source target : Annotation} {level : Nat}
    (admissible : AdmissibleUniverseTranslation source target) :
    HasType .empty (projectedRelation source target level : Term 0)
      (relationFamilyType source level) := by
  exact .relationProjection (universeWitness_hasType admissible)

/-- The source relation family has the same type as the projected canonical witness. -/
theorem sourceRelation_hasType (source : Annotation) (level : Nat) :
    HasType .empty (.relationFamily source level : Term 0)
      (relationFamilyType source level) :=
  .relationFamily .empty source level

/-- A canonical structured-universe projection is one definitional reduction step. -/
theorem projectedRelation_beta (source target : Annotation) (level : Nat) :
    BetaStep (projectedRelation source target level : Term n)
      (.relationFamily source level) :=
  .universeProjection source target level

/-- A canonical structured-universe projection is a definitional conversion. -/
theorem projectedRelation_convertible (source target : Annotation) (level : Nat) :
    Convertible (projectedRelation source target level : Term n)
      (.relationFamily source level) :=
  .beta (projectedRelation_beta source target level)

/-- Canonical projection conversion is preserved by binary-relation application. -/
theorem projectedRelationApplication_convertible (source target : Annotation)
    (level : Nat) (left right : Term n) :
    Convertible
      (relationApplication (projectedRelation source target level) left right)
      (relationApplication (.relationFamily source level) left right) := by
  exact (projectedRelation_convertible source target level).appFunction.appFunction

/-- The complete typing and conversion content of the canonical structured-universe equation. -/
structure SatisfiesUniverseEquation (source target : Annotation) (level : Nat) : Prop where
  /-- The structured universe witness has its relation-family application type. -/
  witnessTyping : HasType .empty (.universeWitness source target level : Term 0)
    (universeWitnessType source target level)
  /-- Its projected relation has the source relation family's binary-relation type. -/
  projectionTyping : HasType .empty (projectedRelation source target level : Term 0)
    (relationFamilyType source level)
  /-- Projection computes definitionally to the source relation family. -/
  projectionConversion : Convertible (projectedRelation source target level : Term 0)
    (.relationFamily source level)

/-- Every admissible annotation pair realizes the canonical structured-universe equation. -/
theorem satisfiesUniverseEquation {source target : Annotation} {level : Nat}
    (admissible : AdmissibleUniverseTranslation source target) :
    SatisfiesUniverseEquation source target level :=
  ⟨universeWitness_hasType admissible, projectedRelation_hasType admissible,
    projectedRelation_convertible source target level⟩

/-- Quotation of a structured witness's relation field in the extended syntax. -/
structure RelationFieldQuotation where
  /-- Project the relation field of an annotation-indexed structured witness. -/
  relationField : {n : Nat} → Annotation → Term n → Term n

/-- The genuine relation-field quotation is the primitive projection constructor. -/
def RelationFieldQuotation.canonical : RelationFieldQuotation where
  relationField := fun _ witness => .relationProjection witness

/-- Apply a quoted relation field to two endpoint terms. -/
def RelationFieldQuotation.application (quotation : RelationFieldQuotation)
    (annotation : Annotation) (witness left right : Term n) : Term n :=
  relationApplication (quotation.relationField annotation witness) left right

/-- Form the projected relation type of the two newest endpoint variables. -/
def RelationFieldQuotation.relatedDomain (quotation : RelationFieldQuotation)
    (annotation : Annotation) (witness : Term n) : Term (n + 2) :=
  quotation.application annotation (witness.weakenBy 2) (.var 1) (.var 0)

/-- Abstract a body witness over original, primed, and projected-relation binders. -/
def RelationFieldQuotation.lambdaWitness (quotation : RelationFieldQuotation)
    (annotation : Annotation) (domain domain' domainWitness : Term n)
    (bodyWitness : Term (n + 3)) : Term n :=
  .lam domain
    (.lam (domain'.weakenBy 1)
      (.lam (quotation.relatedDomain annotation domainWitness) bodyWitness))

/-- The canonical third binder is explicit application of `rel` to both endpoint variables. -/
theorem RelationFieldQuotation.canonical_relatedDomain
    (annotation : Annotation) (witness : Term n) :
    RelationFieldQuotation.canonical.relatedDomain annotation witness =
      relationApplication (.relationProjection (witness.weakenBy 2)) (.var 1) (.var 0) :=
  rfl

/-- Canonical field quotation is typed for every typed structured witness. -/
theorem RelationFieldQuotation.canonical_hasType
    {context : Context n} {witness left right : Term n}
    {target : Annotation} {level : Nat}
    (witnessTyping : HasType context witness
      (structuredRelationType target level left right)) :
    HasType context (RelationFieldQuotation.canonical.relationField target witness)
      (.relationType left right) :=
  .relationProjection witnessTyping

/-- A term is directly core-representable when it is literally in the embedding's image. -/
def CoreRepresentable (term : Term n) : Prop :=
  ∃ core : CoreTerm n, Term.ofCore core = term

/-- The canonical projected-relation binder is not a type from the embedded core syntax. -/
theorem RelationFieldQuotation.not_coreRepresentable_canonical_relatedDomain
    (annotation : Annotation) (witness : Term n) :
    ¬ CoreRepresentable
      (RelationFieldQuotation.canonical.relatedDomain annotation witness) := by
  rintro ⟨core, equal⟩
  have impossible := congrArg Term.toCore? equal
  simp only [Term.toCore?_ofCore, RelationFieldQuotation.relatedDomain,
    RelationFieldQuotation.application, RelationFieldQuotation.canonical,
    relationApplication, Term.toCore?] at impossible
  cases impossible

/-- A genuine relation-family primitive is not directly representable by a core term. -/
theorem not_coreRepresentable_relationFamily (source : Annotation) (level : Nat) :
    ¬ CoreRepresentable (.relationFamily source level : Term n) := by
  rintro ⟨core, equal⟩
  have impossible := congrArg Term.toCore? equal
  simp only [Term.toCore?_ofCore, Term.toCore?] at impossible
  cases impossible

/-- A genuine universe-witness primitive is not directly representable by a core term. -/
theorem not_coreRepresentable_universeWitness
    (source target : Annotation) (level : Nat) :
    ¬ CoreRepresentable (.universeWitness source target level : Term n) := by
  rintro ⟨core, equal⟩
  have impossible := congrArg Term.toCore? equal
  simp only [Term.toCore?_ofCore, Term.toCore?] at impossible
  cases impossible

/-- A genuine relation projection is not directly representable by a core term. -/
theorem not_coreRepresentable_relationProjection (witness : Term n) :
    ¬ CoreRepresentable (.relationProjection witness) := by
  rintro ⟨core, equal⟩
  have impossible := congrArg Term.toCore? equal
  simp only [Term.toCore?_ofCore, Term.toCore?] at impossible
  cases impossible

example {source target : Annotation} {level : Nat}
    (admissible : AdmissibleUniverseTranslation source target) :
    HasType .empty (projectedRelation source target level : Term 0)
      (relationFamilyType source level) :=
  projectedRelation_hasType admissible

example (source target : Annotation) (level : Nat) :
    Convertible (projectedRelation source target level : Term n)
      (.relationFamily source level) :=
  projectedRelation_convertible source target level

/-- The canonical top/top universe witness satisfies the structured quotation equation. -/
theorem satisfiesTopUniverseEquation (level : Nat) :
    SatisfiesUniverseEquation Annotation.equivalence Annotation.equivalence level :=
  satisfiesUniverseEquation
    (admissibleUniverseTranslation_of_equivalence Annotation.equivalence)

universe u

/-- Top structured relations and univalent relation packages are equivalent fiberwise. -/
noncomputable def topStructuredRelationEquivUnivalentRelation (A B : Type u) :
    StructuredRelation.{u, u, u} Annotation.equivalence A B ≃ UnivalentRelation A B :=
  (univalentRelationEquivStructuredRelationTop A B).symm

/-- The native top universe witness has the family of top structured relations as its fibers. -/
@[simp] theorem topSemanticUniverseWitness_fiber
    (univalent : IsUnivalentUniverse.{u}) (A B : Type u) :
    (universeStructuredRelationTop univalent).rel A B =
      StructuredRelation.{u, u, u} Annotation.equivalence A B :=
  rfl

/-- Each native top-universe fiber is equivalent to a univalent relation package. -/
noncomputable def topSemanticUniverseWitnessFiberEquivUnivalentRelation
    (univalent : IsUnivalentUniverse.{u}) (A B : Type u) :
    (universeStructuredRelationTop univalent).rel A B ≃ UnivalentRelation A B :=
  topStructuredRelationEquivUnivalentRelation A B

end DeepWiki.Refine.StructuredUniverseQuotationSyntax
