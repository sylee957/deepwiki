import DeepWiki.Refine.AnnotatedRelationTranslation
import DeepWiki.Refine.WitnessWeakening

/-! # Recursive weakening of dependent witnesses

The object-language recursion for weakening translated witnesses is specified separately from a
native semantic implementation. The former isolates the quotation interface still required by a
fully typed translation; the latter executes universe projection and dependent variance directly.
-/

namespace DeepWiki.Refine.RecursiveWitnessWeakening

open AnnotatedRelationTranslation

/-- Apply an object-language witness transformer to one witness argument. -/
def applyUnaryWitness (transformer witness : Term (relationalScope n)) :
    Term (relationalScope n) :=
  .app transformer witness

/-- No raw application node is syntactically identical to every possible witness term. -/
theorem noSyntacticIdentityTransformer (n : Nat) :
    ¬ ∃ transformer : Term (relationalScope n),
      ∀ witness, applyUnaryWitness transformer witness = witness := by
  rintro ⟨transformer, identity⟩
  have impossible := identity (.sort 0 Annotation.equivalence)
  cases impossible

/-- The object-language identity transformer used by reflexive witness weakening. -/
def identityWitnessTransformer (n : Nat) : Term (relationalScope n) :=
  .lam (.sort 0 Annotation.equivalence) (.var 0)

/-- Applying the identity transformer definitionally beta-reduces to its witness. -/
theorem identityWitnessTransformer_beta (witness : Term (relationalScope n)) :
    AnnotatedDependentCalculus.Convertible (applyUnaryWitness (identityWitnessTransformer n) witness) witness := by
  exact .beta (.beta (.sort 0 Annotation.equivalence) (.var 0) witness)

/-- The body of dependent-product weakening after binding `x`, `x'`, and `xR`. -/
def piWeakeningBody
    (codomainWeakening : Term (relationalScope (n + 1)))
    (sourceWitness domainWeakening : Term (relationalScope n)) :
    Term (relationalScope (n + 1)) :=
  .app codomainWeakening
    (.app
      (.app
        (.app (sourceWitness.weakenBy 3)
          (.var (DependentCalculus.RawParametricity.originalRenaming (n + 1) 0)))
        (.var (DependentCalculus.RawParametricity.primedRenaming (n + 1) 0)))
      (.app (domainWeakening.weakenBy 3)
        (.var (DependentCalculus.RawParametricity.witnessRenaming (n + 1) 0))))

/-- Object-language data needed to state the five recursive witness-weakening equations. -/
structure ObjectWeakeningSpecification where
  /-- Quote the relation witness associated with an annotated type. -/
  relationWitness : {n : Nat} → Term n → Term (relationalScope n)
  /-- Quote primitive componentwise projection between universe relation records. -/
  annotationProjection : {n : Nat} → {low high : Annotation} →
    low ≤ high → Term (relationalScope n)
  /-- Quote the witness transformer associated with a pair of annotated types. -/
  weaken : {n : Nat} → Term n → Term n → Term (relationalScope n)
  /-- Universe weakening converts to primitive projection of relation-record fields. -/
  universeEquation : ∀ {n level : Nat} {low high : Annotation}
      (annotationOrder : low ≤ high) (witness : Term (relationalScope n)),
    AnnotatedDependentCalculus.Convertible (applyUnaryWitness (weaken (.sort level high) (.sort level low)) witness)
      (applyUnaryWitness (annotationProjection annotationOrder) witness)
  /-- Weakening an applied family converts to the recursively weakened indexed witness. -/
  applicationEquation : ∀ {n : Nat} (family family' argument argument' : Term n)
      (witness : Term (relationalScope n)),
    AnnotatedDependentCalculus.Convertible
      (applyUnaryWitness (weaken (.app family argument) (.app family' argument')) witness)
      ((weaken family family').applyWitness argument argument' witness)
  /-- Weakening an applied lambda converts to recursion after substituting both indices. -/
  substitutionEquation : ∀ {n : Nat} (domain domain' : Term n)
      (body body' : Term (n + 1)) (argument argument' : Term n)
      (witness : Term (relationalScope n)),
    AnnotatedDependentCalculus.Convertible
      ((weaken (.lam domain body) (.lam domain' body')).applyWitness
        argument argument' witness)
      (applyUnaryWitness
        (weaken (body.instantiate argument) (body'.instantiate argument')) witness)
  /-- Product weakening converts to backward-domain then forward-codomain transformation. -/
  piEquation : ∀ {n : Nat} (domain domain' : Term n)
      (codomain codomain' : Term (n + 1))
      (witness : Term (relationalScope n)),
    AnnotatedDependentCalculus.Convertible
      (applyUnaryWitness (weaken (.pi domain codomain) (.pi domain' codomain')) witness)
      (AnnotatedRelationTranslation.Term.lambdaWitness domain' domain' (relationWitness domain')
        (piWeakeningBody (weaken codomain codomain') witness
          (weaken domain' domain)))
  /-- Weakening a type to itself is definitionally the identity on witnesses. -/
  identityEquation : ∀ {n : Nat} (source : Term n)
      (witness : Term (relationalScope n)),
    AnnotatedDependentCalculus.Convertible (applyUnaryWitness (weaken source source) witness) witness

/-- Existence of an object-language weakening specification is the missing quotation boundary. -/
def ObjectWeakeningRealizability : Prop :=
  Nonempty ObjectWeakeningSpecification

universe u v w x y z

/-- A directed transformation between two endpoint-indexed witness families. -/
structure WitnessChange {Left : Type u} {Right : Type v}
    (source target : Left → Right → Sort w) where
  /-- Transform a source witness at fixed endpoints into a target witness. -/
  map : ∀ left right, source left right → target left right

/-- The identity transformation on an endpoint-indexed witness family. -/
def WitnessChange.refl {Left : Type u} {Right : Type v}
    (relation : Left → Right → Sort w) : WitnessChange relation relation where
  map := fun _ _ witness => witness

/-- Compose two directed witness transformations. -/
def WitnessChange.comp {Left : Type u} {Right : Type v}
    {first second third : Left → Right → Sort w}
    (outer : WitnessChange second third) (inner : WitnessChange first second) :
    WitnessChange first third where
  map := fun left right witness => outer.map left right (inner.map left right witness)

/-- Evaluate a family-level witness transformation after substituting its two indices. -/
def WitnessChange.substitute {Left : Type u} {Right : Type v}
    {source target : Left → Right → Sort w} (change : WitnessChange source target)
    (left : Left) (right : Right) (witness : source left right) : target left right :=
  change.map left right witness

/-- Componentwise annotation projection weakens structured universe witnesses. -/
def universeWitnessChange {low high : Annotation} (annotationOrder : low ≤ high) :
    WitnessChange
      (fun A B : Type u => StructuredRelation.{u, u, u} high A B)
      (fun A B : Type u => StructuredRelation.{u, u, u} low A B) where
  map := fun _ _ witness => witness.weaken annotationOrder

/-- A dependent-product witness maps related inputs to related outputs. -/
def PiWitness {LeftDomain : Type u} {RightDomain : Type v}
    (domainRelation : LeftDomain → RightDomain → Sort w)
    {LeftCodomain : LeftDomain → Type x} {RightCodomain : RightDomain → Type y}
    (codomainRelation : ∀ left right, domainRelation left right →
      LeftCodomain left → RightCodomain right → Sort z)
    (leftFunction : ∀ left, LeftCodomain left)
    (rightFunction : ∀ right, RightCodomain right) : Sort _ :=
  ∀ left right (related : domainRelation left right),
    codomainRelation left right related (leftFunction left) (rightFunction right)

/-- Recursively weaken a dependent-product witness contravariantly then covariantly. -/
def piWitnessWeakening {LeftDomain : Type u} {RightDomain : Type v}
    {sourceDomain targetDomain : LeftDomain → RightDomain → Sort w}
    {LeftCodomain : LeftDomain → Type x} {RightCodomain : RightDomain → Type y}
    {sourceCodomain : ∀ left right, sourceDomain left right →
      LeftCodomain left → RightCodomain right → Sort z}
    {targetCodomain : ∀ left right, targetDomain left right →
      LeftCodomain left → RightCodomain right → Sort z}
    (domainBackward : WitnessChange targetDomain sourceDomain)
    (codomainForward : ∀ left right (related : targetDomain left right),
      WitnessChange
        (sourceCodomain left right (domainBackward.map left right related))
        (targetCodomain left right related))
    {leftFunction : ∀ left, LeftCodomain left}
    {rightFunction : ∀ right, RightCodomain right}
    (sourceWitness :
      PiWitness sourceDomain sourceCodomain leftFunction rightFunction) :
    PiWitness targetDomain targetCodomain leftFunction rightFunction :=
  fun left right related =>
    (codomainForward left right related).map (leftFunction left) (rightFunction right)
      (sourceWitness left right (domainBackward.map left right related))

/-- Native application weakening evaluates the recursively transformed family witness. -/
def applicationWitnessWeakening {Left : Type u} {Right : Type v}
    {source target : Left → Right → Sort w} (familyWeakening : WitnessChange source target)
    (left : Left) (right : Right) (witness : source left right) : target left right :=
  familyWeakening.map left right witness

/-- Native lambda weakening resumes its body transformation after endpoint substitution. -/
def substitutionWitnessWeakening {Left : Type u} {Right : Type v}
    {source target : Left → Right → Sort w}
    (bodyWeakening : ∀ left right, source left right → target left right)
    (left : Left) (right : Right) (witness : source left right) : target left right :=
  bodyWeakening left right witness

/-- Identity weakening leaves every native witness definitionally unchanged. -/
@[simp] theorem WitnessChange.refl_map {Left : Type u} {Right : Type v}
    (relation : Left → Right → Sort w) (left : Left) (right : Right)
    (witness : relation left right) :
    (WitnessChange.refl relation).map left right witness = witness :=
  rfl

/-- Universe witness weakening preserves the underlying heterogeneous relation. -/
@[simp] theorem universeWitnessChange_rel {low high : Annotation}
    (annotationOrder : low ≤ high) (A B : Type u)
    (witness : StructuredRelation.{u, u, u} high A B) :
    ((universeWitnessChange annotationOrder).map A B witness).rel = witness.rel :=
  rfl

/-- Dependent-product weakening unfolds to backward domain and forward codomain recursion. -/
@[simp] theorem piWitnessWeakening_apply
    {LeftDomain : Type u} {RightDomain : Type v}
    {sourceDomain targetDomain : LeftDomain → RightDomain → Sort w}
    {LeftCodomain : LeftDomain → Type x} {RightCodomain : RightDomain → Type y}
    {sourceCodomain : ∀ left right, sourceDomain left right →
      LeftCodomain left → RightCodomain right → Sort z}
    {targetCodomain : ∀ left right, targetDomain left right →
      LeftCodomain left → RightCodomain right → Sort z}
    (domainBackward : WitnessChange targetDomain sourceDomain)
    (codomainForward : ∀ left right (related : targetDomain left right),
      WitnessChange
        (sourceCodomain left right (domainBackward.map left right related))
        (targetCodomain left right related))
    {leftFunction : ∀ left, LeftCodomain left}
    {rightFunction : ∀ right, RightCodomain right}
    (sourceWitness : PiWitness sourceDomain sourceCodomain leftFunction rightFunction)
    (left : LeftDomain) (right : RightDomain) (related : targetDomain left right) :
    piWitnessWeakening domainBackward codomainForward sourceWitness left right related =
      (codomainForward left right related).map (leftFunction left) (rightFunction right)
        (sourceWitness left right (domainBackward.map left right related)) :=
  rfl

example (specification : ObjectWeakeningSpecification)
    {n level : Nat} {low high : Annotation} (annotationOrder : low ≤ high)
    (witness : Term (relationalScope n)) :
    AnnotatedDependentCalculus.Convertible
      (applyUnaryWitness (specification.weaken (.sort level high) (.sort level low)) witness)
      (applyUnaryWitness (specification.annotationProjection annotationOrder) witness) :=
  specification.universeEquation annotationOrder witness

example (specification : ObjectWeakeningSpecification) {n : Nat}
    (family family' argument argument' : Term n)
    (witness : Term (relationalScope n)) :
    AnnotatedDependentCalculus.Convertible
      (applyUnaryWitness
        (specification.weaken (.app family argument) (.app family' argument')) witness)
      ((specification.weaken family family').applyWitness argument argument' witness) :=
  specification.applicationEquation family family' argument argument' witness

example (specification : ObjectWeakeningSpecification) {n : Nat}
    (domain domain' : Term n) (body body' : Term (n + 1))
    (argument argument' : Term n) (witness : Term (relationalScope n)) :
    AnnotatedDependentCalculus.Convertible
      ((specification.weaken (.lam domain body) (.lam domain' body')).applyWitness
        argument argument' witness)
      (applyUnaryWitness (specification.weaken (body.instantiate argument)
        (body'.instantiate argument')) witness) :=
  specification.substitutionEquation domain domain' body body' argument argument' witness

example (specification : ObjectWeakeningSpecification) {n : Nat}
    (domain domain' : Term n) (codomain codomain' : Term (n + 1))
    (witness : Term (relationalScope n)) :
    AnnotatedDependentCalculus.Convertible
      (applyUnaryWitness
        (specification.weaken (.pi domain codomain) (.pi domain' codomain')) witness)
      (AnnotatedRelationTranslation.Term.lambdaWitness domain' domain' (specification.relationWitness domain')
        (piWeakeningBody (specification.weaken codomain codomain') witness
          (specification.weaken domain' domain))) :=
  specification.piEquation domain domain' codomain codomain' witness

example (specification : ObjectWeakeningSpecification) {n : Nat}
    (source : Term n)
    (witness : Term (relationalScope n)) :
    AnnotatedDependentCalculus.Convertible (applyUnaryWitness (specification.weaken source source) witness) witness :=
  specification.identityEquation source witness

example {low high : Annotation} (annotationOrder : low ≤ high) (A B : Type u)
    (witness : StructuredRelation.{u, u, u} high A B) :
    StructuredRelation.{u, u, u} low A B :=
  (universeWitnessChange annotationOrder).map A B witness

example {Left : Type u} {Right : Type v} {source target : Left → Right → Sort w}
    (change : WitnessChange source target) (left : Left) (right : Right)
    (witness : source left right) : target left right :=
  applicationWitnessWeakening change left right witness

end DeepWiki.Refine.RecursiveWitnessWeakening
