import DeepWiki.Refine.RecursiveWitnessWeakening

/-! # Subtyping-indexed recursive witness weakening

Type-valued structural indices refine the proof-irrelevant annotated subtyping judgment. A
syntactic identity conversion is separated from conversion between distinct beta-convertible
endpoints, while binder substitution is recorded as an additional realizability obligation.
-/

namespace DeepWiki.Refine.RecursiveWitnessWeakeningSubtypeIndexed

open AnnotatedRelationTranslation

/-- Annotated terms used by the subtyping-indexed weakening classification. -/
abbrev Term := AnnotatedDependentCalculus.Term

/-- Annotated contexts used by the subtyping-indexed weakening classification. -/
abbrev Context := AnnotatedDependentCalculus.Context

/-- Atomic heads of the constant-free annotated term grammar. -/
inductive IsAtomic : {n : Nat} → Term n → Prop where
  /-- A scoped type variable is atomic. -/
  | var {n : Nat} (index : Fin n) : IsAtomic (.var index)

/-- Why an annotated conversion cannot use the atomic identity fallback. -/
inductive ConversionBoundary : {n : Nat} → Term n → Term n → Type where
  /-- Beta-convertible but syntactically distinct endpoints need quotient or normalization data. -/
  | distinct {n : Nat} {left right : Term n} (endpointsDistinct : left ≠ right) :
      ConversionBoundary left right
  /-- A reflexive conversion at a composite term overlaps a prior structural clause. -/
  | compositeIdentity {n : Nat} {source : Term n} (notAtomic : ¬ IsAtomic source) :
      ConversionBoundary source source

/-- A proof-relevant structural index whose erasure is an annotated subtyping derivation. -/
inductive TypedDerivation : {n : Nat} → Context n → Term n → Term n → Type where
  /-- Syntactically equal atomic, well-kinded endpoints select the identity fallback. -/
  | identity {n : Nat} {context : Context n} {source kind : Term n}
      (atomic : IsAtomic source)
      (kindShape : AnnotatedDependentCalculus.IsKind kind)
      (sourceWellTyped : AnnotatedDependentCalculus.HasType context source kind) :
      TypedDerivation context source source
  /-- Non-atomic or distinct beta-convertible endpoints remain an explicit boundary. -/
  | conversionBoundary {n : Nat} {context : Context n} {left right kind : Term n}
      (kindShape : AnnotatedDependentCalculus.IsKind kind)
      (leftWellTyped : AnnotatedDependentCalculus.HasType context left kind)
      (rightWellTyped : AnnotatedDependentCalculus.HasType context right kind)
      (equal : AnnotatedDependentCalculus.Convertible left right)
      (boundary : ConversionBoundary left right) :
      TypedDerivation context left right
  /-- Universe subtyping records annotation weakening and cumulative level growth. -/
  | universe {n : Nat} {context : Context n} {source target : Annotation}
      {lower upper : Nat} (annotationOrder : target ≤ source)
      (levelOrder : lower ≤ upper) :
      TypedDerivation context (.sort lower source) (.sort upper target)
  /-- Application subtyping recursively indexes its function derivation. -/
  | application {n : Nat} {context : Context n}
      {function function' argument kind : Term n}
      (kindShape : AnnotatedDependentCalculus.IsKind kind)
      (targetWellTyped :
        AnnotatedDependentCalculus.HasType context (.app function' argument) kind)
      (functionDerivation : TypedDerivation context function function') :
      TypedDerivation context (.app function argument) (.app function' argument)
  /-- Lambda subtyping recursively indexes its body derivation under the common domain. -/
  | lambda {n : Nat} {context : Context n} {domain : Term n}
      {body body' : Term (n + 1)}
      (bodyDerivation : TypedDerivation (.extend context domain) body body') :
      TypedDerivation context (.lam domain body) (.lam domain body')
  /-- Product subtyping indexes its contravariant domain and covariant codomain derivations. -/
  | pi {n : Nat} {context : Context n} {domain domain' : Term n}
      {codomain codomain' : Term (n + 1)} {level : Nat}
      {outputAnnotation : Annotation}
      (productWellTyped : AnnotatedDependentCalculus.HasType context
        (.pi domain codomain) (.sort level outputAnnotation))
      (domainDerivation : TypedDerivation context domain' domain)
      (codomainDerivation :
        TypedDerivation (.extend context domain') codomain codomain') :
      TypedDerivation context (.pi domain codomain) (.pi domain' codomain')

/-- Forget a proof-relevant structural index to ordinary annotated subtyping. -/
theorem TypedDerivation.toSubtype :
    TypedDerivation context source target →
      AnnotatedDependentCalculus.Subtype context source target
  | .identity _ kindShape sourceWellTyped =>
      .conversion kindShape sourceWellTyped sourceWellTyped (.refl _)
  | .conversionBoundary kindShape leftWellTyped rightWellTyped equal _ =>
      .conversion kindShape leftWellTyped rightWellTyped equal
  | .universe annotationOrder levelOrder => .sort annotationOrder levelOrder
  | .application kindShape targetWellTyped functionDerivation =>
      .app kindShape targetWellTyped functionDerivation.toSubtype
  | .lambda bodyDerivation => .lam bodyDerivation.toSubtype
  | .pi productWellTyped domainDerivation codomainDerivation =>
      .pi productWellTyped domainDerivation.toSubtype codomainDerivation.toSubtype

/-- A typed structural index covers its endpoint subtyping proposition. -/
def TypedDerivation.Covers (derivation : TypedDerivation context source target)
    (subtype : AnnotatedDependentCalculus.Subtype context source target) : Prop :=
  derivation.toSubtype = subtype

/-- Proof irrelevance identifies the erased index with any derivation of the same subtyping fact. -/
theorem TypedDerivation.covers (derivation : TypedDerivation context source target)
    (subtype : AnnotatedDependentCalculus.Subtype context source target) :
    derivation.Covers subtype := by
  exact Subsingleton.elim _ _

/-- Every annotated conversion is classified as atomic identity or an explicit boundary. -/
theorem conversion_coverage {context : Context n} {left right kind : Term n}
    (kindShape : AnnotatedDependentCalculus.IsKind kind)
    (leftWellTyped : AnnotatedDependentCalculus.HasType context left kind)
    (rightWellTyped : AnnotatedDependentCalculus.HasType context right kind)
    (equal : AnnotatedDependentCalculus.Convertible left right) :
    Nonempty (TypedDerivation context left right) := by
  by_cases endpointsEqual : left = right
  · subst right
    by_cases atomic : IsAtomic left
    · exact ⟨.identity atomic kindShape leftWellTyped⟩
    · exact ⟨.conversionBoundary kindShape leftWellTyped rightWellTyped equal
        (.compositeIdentity atomic)⟩
  · exact ⟨.conversionBoundary kindShape leftWellTyped rightWellTyped equal
      (.distinct endpointsEqual)⟩

/-- Every constructor of annotated subtyping has a proof-relevant structural index. -/
theorem subtype_coverage {context : Context n} {source target : Term n}
    (subtype : AnnotatedDependentCalculus.Subtype context source target) :
    Nonempty (TypedDerivation context source target) := by
  exact AnnotatedDependentCalculus.Subtype.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun context source target _ =>
      Nonempty (TypedDerivation context source target))
    (by trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by
      intro n context left right kind kindShape leftWellTyped rightWellTyped equal _ _
      exact conversion_coverage kindShape leftWellTyped rightWellTyped equal)
    (by
      intro n context source target lower upper annotationOrder levelOrder
      exact ⟨.universe annotationOrder levelOrder⟩)
    (by
      intro n context function function' argument kind kindShape targetWellTyped
        functionSubtype _ functionHypothesis
      obtain ⟨functionDerivation⟩ := functionHypothesis
      exact ⟨.application kindShape targetWellTyped functionDerivation⟩)
    (by
      intro n context domain body body' bodySubtype bodyHypothesis
      obtain ⟨bodyDerivation⟩ := bodyHypothesis
      exact ⟨.lambda bodyDerivation⟩)
    (by
      intro n context domain domain' codomain codomain' level outputAnnotation
        productWellTyped domainSubtype codomainSubtype _ domainHypothesis codomainHypothesis
      obtain ⟨domainDerivation⟩ := domainHypothesis
      obtain ⟨codomainDerivation⟩ := codomainHypothesis
      exact ⟨.pi productWellTyped domainDerivation codomainDerivation⟩)
    subtype

/-- A noncomputable structural index can be selected for every annotated subtyping fact. -/
noncomputable def indexSubtype {context : Context n} {source target : Term n}
    (subtype : AnnotatedDependentCalculus.Subtype context source target) :
    TypedDerivation context source target :=
  Classical.choice (subtype_coverage subtype)

/-- The selected structural index erases back to the given subtyping proposition. -/
theorem indexSubtype_covers {context : Context n} {source target : Term n}
    (subtype : AnnotatedDependentCalculus.Subtype context source target) :
    (indexSubtype subtype).Covers subtype :=
  (indexSubtype subtype).covers subtype

/-- Binder recursion data needed to turn lambda subtyping into the paired-substitution clause. -/
structure LambdaSubstitutionClosure {n : Nat} {context : Context n}
    {domain : Term n} {body body' : Term (n + 1)}
    (bodyDerivation : TypedDerivation (.extend context domain) body body') : Type where
  /-- Index weakening after independently substituting the two translated endpoints. -/
  instantiate : ∀ argument argument' : Term n,
    TypedDerivation context (body.instantiate argument) (body'.instantiate argument')

/-- The five object-language weakening equations indexed by actual typed subtyping structure. -/
structure ObjectWeakeningSpecification where
  /-- Quote the relation witness associated with an annotated type. -/
  relationWitness : {n : Nat} → Term n → Term (relationalScope n)
  /-- Quote primitive componentwise projection between universe relation records. -/
  annotationProjection : {n : Nat} → {low high : Annotation} →
    low ≤ high → Term (relationalScope n)
  /-- Quote the transformer selected by a proof-relevant typed derivation. -/
  weaken : {n : Nat} → {context : Context n} → {source target : Term n} →
    TypedDerivation context source target → Term (relationalScope n)
  /-- Universe weakening is the primitive annotation projection. -/
  universeEquation : ∀ {n lower upper : Nat} (context : Context n)
      {source target : Annotation} (annotationOrder : target ≤ source)
      (levelOrder : lower ≤ upper) (witness : Term (relationalScope n)),
    AnnotatedDependentCalculus.Convertible
      (RecursiveWitnessWeakening.applyUnaryWitness
        (weaken (TypedDerivation.universe (context := context)
          annotationOrder levelOrder)) witness)
      (RecursiveWitnessWeakening.applyUnaryWitness
        (annotationProjection annotationOrder) witness)
  /-- Application weakening invokes its recursively selected function transformer. -/
  applicationEquation : ∀ {n : Nat} {context : Context n}
      {function function' argument kind : Term n}
      (kindShape : AnnotatedDependentCalculus.IsKind kind)
      (targetWellTyped :
        AnnotatedDependentCalculus.HasType context (.app function' argument) kind)
      (functionDerivation : TypedDerivation context function function')
      (witness : Term (relationalScope n)),
    AnnotatedDependentCalculus.Convertible
      (RecursiveWitnessWeakening.applyUnaryWitness
        (weaken (.application kindShape targetWellTyped functionDerivation)) witness)
      (AnnotatedRelationTranslation.Term.applyWitness
        (weaken functionDerivation) argument argument witness)
  /-- Lambda weakening resumes body recursion after substituting both endpoints. -/
  lambdaEquation : ∀ {n : Nat} {context : Context n} {domain : Term n}
      {body body' : Term (n + 1)}
      (bodyDerivation : TypedDerivation (.extend context domain) body body')
      (substitution : LambdaSubstitutionClosure bodyDerivation)
      (argument argument' : Term n) (witness : Term (relationalScope n)),
    AnnotatedDependentCalculus.Convertible
      (AnnotatedRelationTranslation.Term.applyWitness
        (weaken (.lambda bodyDerivation)) argument argument' witness)
      (RecursiveWitnessWeakening.applyUnaryWitness
        (weaken (substitution.instantiate argument argument')) witness)
  /-- Product weakening performs backward-domain then forward-codomain recursion. -/
  piEquation : ∀ {n : Nat} {context : Context n} {domain domain' : Term n}
      {codomain codomain' : Term (n + 1)} {level : Nat}
      {outputAnnotation : Annotation}
      (productWellTyped : AnnotatedDependentCalculus.HasType context
        (.pi domain codomain) (.sort level outputAnnotation))
      (domainDerivation : TypedDerivation context domain' domain)
      (codomainDerivation :
        TypedDerivation (.extend context domain') codomain codomain')
      (witness : Term (relationalScope n)),
    AnnotatedDependentCalculus.Convertible
      (RecursiveWitnessWeakening.applyUnaryWitness
        (weaken (.pi productWellTyped domainDerivation codomainDerivation)) witness)
      (Term.lambdaWitness domain' domain' (relationWitness domain')
        (RecursiveWitnessWeakening.piWeakeningBody
          (weaken codomainDerivation) witness (weaken domainDerivation)))
  /-- Atomic identity weakening beta-converts to the original witness. -/
  identityEquation : ∀ {n : Nat} {context : Context n} {source kind : Term n}
      (atomic : IsAtomic source)
      (kindShape : AnnotatedDependentCalculus.IsKind kind)
      (sourceWellTyped : AnnotatedDependentCalculus.HasType context source kind)
      (witness : Term (relationalScope n)),
    AnnotatedDependentCalculus.Convertible
      (RecursiveWitnessWeakening.applyUnaryWitness
        (weaken (.identity atomic kindShape sourceWellTyped)) witness) witness

/-- Lambda subtyping alone exposes a body index but not paired-endpoint substitution closure. -/
structure LambdaWeakeningIndex {n : Nat} {context : Context n} {domain : Term n}
    {body body' : Term (n + 1)} : Type where
  /-- The actual subtyping derivation under the shared source domain. -/
  body : TypedDerivation (.extend context domain) body body'
  /-- The extra closure required by the paired-endpoint substitution equation. -/
  substitution : LambdaSubstitutionClosure body

/-- A lambda weakening index yields its actual annotated lambda subtyping derivation. -/
def LambdaWeakeningIndex.toTypedDerivation
    {n : Nat} {context : Context n} {domain : Term n}
    {bodyTerm bodyTerm' : Term (n + 1)}
    (index : LambdaWeakeningIndex (context := context) (domain := domain)
      (body := bodyTerm) (body' := bodyTerm')) :
    TypedDerivation context (.lam domain bodyTerm) (.lam domain bodyTerm') :=
  .lambda index.body

/-- Structural indices supported by the five recursive weakening equations. -/
inductive Supported : TypedDerivation context source target → Prop where
  /-- Syntactic identity conversion is supported by the identity equation. -/
  | identity {kind : Term n} {kindShape : AnnotatedDependentCalculus.IsKind kind}
      {atomic : IsAtomic source}
      {sourceWellTyped : AnnotatedDependentCalculus.HasType context source kind} :
      Supported (.identity atomic kindShape sourceWellTyped)
  /-- Universe weakening is supported directly. -/
  | universe {sourceAnnotation targetAnnotation : Annotation} {lower upper : Nat}
      {annotationOrder : targetAnnotation ≤ sourceAnnotation}
      {levelOrder : lower ≤ upper} :
      Supported (.universe (context := context) annotationOrder levelOrder)
  /-- Application weakening is supported when its recursive function index is supported. -/
  | application {function function' argument kind : Term n}
      {kindShape : AnnotatedDependentCalculus.IsKind kind}
      {targetWellTyped :
        AnnotatedDependentCalculus.HasType context (.app function' argument) kind}
      {functionDerivation : TypedDerivation context function function'}
      (functionSupported : Supported functionDerivation) :
      Supported (.application kindShape targetWellTyped functionDerivation)
  /-- Products are supported when both variance-recursive indices are supported. -/
  | pi {domain domain' : Term n} {codomain codomain' : Term (n + 1)}
      {level : Nat} {outputAnnotation : Annotation}
      {productWellTyped : AnnotatedDependentCalculus.HasType context
        (.pi domain codomain) (.sort level outputAnnotation)}
      {domainDerivation : TypedDerivation context domain' domain}
      {codomainDerivation :
        TypedDerivation (.extend context domain') codomain codomain'}
      (domainSupported : Supported domainDerivation)
      (codomainSupported : Supported codomainDerivation) :
      Supported (.pi productWellTyped domainDerivation codomainDerivation)
  /-- Lambda support additionally carries paired-endpoint substitution indices. -/
  | lambda {domain : Term n} {body body' : Term (n + 1)}
      {bodyDerivation : TypedDerivation (.extend context domain) body body'}
      (substitution : LambdaSubstitutionClosure bodyDerivation) :
      Supported (.lambda bodyDerivation)

/-- Distinct-endpoint conversion boundaries have no structural weakening equation. -/
theorem not_supported_conversionBoundary {context : Context n} {left right kind : Term n}
    (kindShape : AnnotatedDependentCalculus.IsKind kind)
    (leftWellTyped : AnnotatedDependentCalculus.HasType context left kind)
    (rightWellTyped : AnnotatedDependentCalculus.HasType context right kind)
    (equal : AnnotatedDependentCalculus.Convertible left right)
    (boundary : ConversionBoundary left right) :
    ¬ Supported (.conversionBoundary kindShape leftWellTyped rightWellTyped equal boundary) := by
  intro supported
  cases supported

/-- Type-valued weakening operators may compute from proof-relevant structural indices. -/
structure TypedWeakeningRealizers where
  /-- Realize the universe relation constructor. -/
  universeRule : {n : Nat} → Annotation → Annotation → Nat → UniverseWitness n
  /-- Realize the non-dependent arrow relation constructor. -/
  arrow : {n : Nat} → Annotation → ArrowWitnessOperator n
  /-- Realize the dependent-product relation constructor. -/
  pi : {n : Nat} → Annotation → PiWitnessOperator n
  /-- Realize weakening from a proof-relevant structural index. -/
  weakening : {n : Nat} → (context : AnnotatedRelationTranslation.Context n) →
    {source target : Term n} →
    TypedDerivation context.gamma source target → WitnessWeakening n

/-- Select a typed weakening operator through the canonical noncomputable subtype index. -/
noncomputable def TypedWeakeningRealizers.selectedWeakening
    (realizers : TypedWeakeningRealizers) {n : Nat}
    (context : AnnotatedRelationTranslation.Context n) {source target : Term n}
    (subtype : AnnotatedDependentCalculus.Subtype context.gamma source target) :
    WitnessWeakening n :=
  realizers.weakening context (indexSubtype subtype)

/-- Choosing one structural index per subtype induces the translation's weakening field. -/
noncomputable def TypedWeakeningRealizers.toSyntaxRealizers
    (realizers : TypedWeakeningRealizers) : AnnotatedRelationTranslation.SyntaxRealizers where
  universeRule := realizers.universeRule
  arrow := realizers.arrow
  pi := realizers.pi
  weakening := realizers.selectedWeakening

/-- A beta-redex and its contractum form a genuine distinct-endpoint conversion boundary. -/
def betaConversionBoundary :
    TypedDerivation AnnotatedDependentCalculus.Context.empty
      (.app
        (.lam (.sort 1 Annotation.equivalence) (.var 0))
        (.sort 0 Annotation.equivalence))
      (.sort 0 Annotation.equivalence) := by
  let emptyWellFormed : AnnotatedDependentCalculus.WellFormed
      AnnotatedDependentCalculus.Context.empty := .empty
  let domainWellTyped : AnnotatedDependentCalculus.HasType
      AnnotatedDependentCalculus.Context.empty
      (.sort 1 Annotation.equivalence) (.sort 2 Annotation.equivalence) :=
    .sort emptyWellFormed (admissibleUniverseTranslation_of_equivalence _) 1
  let extendedWellFormed : AnnotatedDependentCalculus.WellFormed
      (.extend AnnotatedDependentCalculus.Context.empty
        (.sort 1 Annotation.equivalence)) :=
    .extend emptyWellFormed domainWellTyped
  let bodyWellTyped : AnnotatedDependentCalculus.HasType
      (.extend AnnotatedDependentCalculus.Context.empty
        (.sort 1 Annotation.equivalence))
      (.var 0) (.sort 1 Annotation.equivalence) := by
    simpa [AnnotatedDependentCalculus.Context.lookup,
      AnnotatedDependentCalculus.Term.rename] using
      AnnotatedDependentCalculus.HasType.var extendedWellFormed 0
  let functionWellTyped : AnnotatedDependentCalculus.HasType
      AnnotatedDependentCalculus.Context.empty
      (.lam (.sort 1 Annotation.equivalence) (.var 0))
      (.pi (.sort 1 Annotation.equivalence) (.sort 1 Annotation.equivalence)) :=
    .lam bodyWellTyped
  let argumentWellTyped : AnnotatedDependentCalculus.HasType
      AnnotatedDependentCalculus.Context.empty
      (.sort 0 Annotation.equivalence) (.sort 1 Annotation.equivalence) :=
    .sort emptyWellFormed (admissibleUniverseTranslation_of_equivalence _) 0
  let redexWellTyped : AnnotatedDependentCalculus.HasType
      AnnotatedDependentCalculus.Context.empty
      (.app
        (.lam (.sort 1 Annotation.equivalence) (.var 0))
        (.sort 0 Annotation.equivalence))
      (.sort 1 Annotation.equivalence) := by
    simpa [AnnotatedDependentCalculus.Term.instantiate,
      AnnotatedDependentCalculus.Term.substitute,
      AnnotatedDependentCalculus.Substitution.single] using
      AnnotatedDependentCalculus.HasType.app functionWellTyped argumentWellTyped
  exact .conversionBoundary
    (.sort 1 Annotation.equivalence) redexWellTyped argumentWellTyped
    (.beta (.beta (.sort 1 Annotation.equivalence) (.var 0)
      (.sort 0 Annotation.equivalence))) (.distinct (by intro equal; cases equal))

/-- The concrete beta-conversion boundary cannot be assigned a structural weakening equation. -/
theorem not_supported_betaConversionBoundary : ¬ Supported betaConversionBoundary := by
  unfold betaConversionBoundary
  apply not_supported_conversionBoundary

/-- No typed index between the concrete beta-redex and contractum belongs to the structural fragment. -/
theorem no_supported_betaConversionIndex
    (derivation :
      TypedDerivation AnnotatedDependentCalculus.Context.empty
        (.app
          (.lam (.sort 1 Annotation.equivalence) (.var 0))
          (.sort 0 Annotation.equivalence))
        (.sort 0 Annotation.equivalence)) :
    ¬ Supported derivation := by
  intro supported
  cases supported

/-- Distinct beta-convertible endpoints refute coverage by the five structural equations alone. -/
theorem not_fullStructuralSupport :
    ¬ ∀ {n : Nat} {context : Context n} {source target : Term n}
      (subtype : AnnotatedDependentCalculus.Subtype context source target),
      Supported (indexSubtype subtype) := by
  intro support
  exact no_supported_betaConversionIndex
    (indexSubtype betaConversionBoundary.toSubtype)
    (support betaConversionBoundary.toSubtype)

example {context : Context n} {source target : Term n}
    (subtype : AnnotatedDependentCalculus.Subtype context source target) :
    Nonempty (TypedDerivation context source target) :=
  subtype_coverage subtype

noncomputable example (realizers : TypedWeakeningRealizers) :
    AnnotatedRelationTranslation.SyntaxRealizers :=
  realizers.toSyntaxRealizers

end DeepWiki.Refine.RecursiveWitnessWeakeningSubtypeIndexed
