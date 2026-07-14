import DeepWiki.Refine.AnnotatedDependentCalculus

/-! # Registered constants

Global constants may admit several annotated types with one common erasure. A partial,
annotation-indexed registry supplies the primed constant and its relation witness.
-/

namespace DeepWiki.Refine.RegisteredConstants

open AnnotatedDependentCalculus

/-- A closed annotated type suitable for assignment to a global constant. -/
abbrev ClosedAnnotatedType := AnnotatedDependentCalculus.Term 0

/-- A closed annotated term is a type when it inhabits some annotated universe. -/
def IsAnnotatedType (type : ClosedAnnotatedType) : Prop :=
  ∃ level annotation,
    AnnotatedDependentCalculus.HasType AnnotatedDependentCalculus.Context.empty type
      (.sort level annotation)

/-- A global constant registry with annotation-indexed relational translations. -/
structure Registry (Constant : Type u) (Output : Type w) where
  /-- The constants belonging to the global environment. -/
  declared : Constant → Prop
  /-- The collection of admissible annotated types assigned to each constant. -/
  annotatedType : Constant → ClosedAnnotatedType → Prop
  /-- Every member of a constant's annotated-type collection is a well-typed closed type. -/
  annotatedTypeWellTyped : ∀ {constant type}, annotatedType constant type → IsAnnotatedType type
  /-- All annotated types assigned to one constant have the same erasure. -/
  sameErasure : ∀ {constant type₁ type₂},
    annotatedType constant type₁ → annotatedType constant type₂ →
      type₁.erase = type₂.erase
  /-- Look up the primed constant and relation witness registered at an annotated type. -/
  translation : Constant → ClosedAnnotatedType → Option (Output × Output)
  /-- Predicate recognizing well-formed global output terms. -/
  outputWellFormed : Output → Prop
  /-- Every successful lookup returns well-formed output terms. -/
  translationWellFormed : ∀ {constant type primed witness},
    translation constant type = some (primed, witness) →
      outputWellFormed primed ∧ outputWellFormed witness
  /-- Every successful lookup is indexed by a declared constant and one of its annotated types. -/
  translationSourceValid : ∀ {constant type primed witness},
    translation constant type = some (primed, witness) →
      declared constant ∧ annotatedType constant type

/-- A registered translation maps `constant` at `type` to `primed` with witness `witness`. -/
def RegisteredTranslation (registry : Registry Constant Output) (constant : Constant)
    (type : ClosedAnnotatedType) (primed witness : Output) : Prop :=
  registry.translation constant type = some (primed, witness)

/-- A registry is complete when every admissible type of every declared constant has a translation. -/
def Registry.IsComplete (registry : Registry Constant Output) : Prop :=
  ∀ {constant type}, registry.declared constant → registry.annotatedType constant type →
    ∃ primed witness, RegisteredTranslation registry constant type primed witness

/-- The positive constant-typing rule is membership in the constant and type collections. -/
inductive PositiveTyping (registry : Registry Constant Output) :
    {n : Nat} → Context n → Constant → ClosedAnnotatedType → Prop where
  /-- A declared constant has every annotated type in its associated collection. -/
  | constant {n : Nat} {context : Context n} {name : Constant}
      {type : ClosedAnnotatedType}
      (nameDeclared : registry.declared name)
      (typeAllowed : registry.annotatedType name type) :
      PositiveTyping registry context name type

/-- Registered-constant translation is an annotation-indexed database lookup. -/
inductive RegisteredConstantTranslation (registry : Registry Constant Output)
    {TranslationContext : Type v}
    (context : TranslationContext) :
    Constant → ClosedAnnotatedType → Output → Output → Prop where
  /-- A successful registry lookup translates a constant independently of the local context. -/
  | registered {name : Constant} {type : ClosedAnnotatedType} {primed witness : Output}
      (entry : RegisteredTranslation registry name type primed witness) :
      RegisteredConstantTranslation registry context name type primed witness

/-- A constant/type pair is stuck exactly when its translation lookup returns no entry. -/
def IsStuck (registry : Registry Constant Output) (constant : Constant)
    (type : ClosedAnnotatedType) : Prop :=
  registry.translation constant type = none

/-- Positive constant typing exposes declaration of the source constant. -/
theorem PositiveTyping.declared
    {registry : Registry Constant Output} {context : Context n} {constant : Constant}
    {type : ClosedAnnotatedType}
    (typing : PositiveTyping registry context constant type) :
    registry.declared constant := by
  cases typing with
  | constant nameDeclared _ => exact nameDeclared

/-- Positive constant typing exposes membership of the selected annotated type. -/
theorem PositiveTyping.annotatedType
    {registry : Registry Constant Output} {context : Context n} {constant : Constant}
    {type : ClosedAnnotatedType}
    (typing : PositiveTyping registry context constant type) :
    registry.annotatedType constant type := by
  cases typing with
  | constant _ typeAllowed => exact typeAllowed

/-- Positive constant typing ensures that the selected annotation is a well-typed closed type. -/
theorem PositiveTyping.typeWellTyped
    {registry : Registry Constant Output} {context : Context n} {constant : Constant}
    {type : ClosedAnnotatedType}
    (typing : PositiveTyping registry context constant type) :
    IsAnnotatedType type :=
  registry.annotatedTypeWellTyped typing.annotatedType

/-- Two positive type assignments for one constant erase to the same ordinary type. -/
theorem PositiveTyping.erase_eq
    {registry : Registry Constant Output} {context₁ : Context n₁} {context₂ : Context n₂}
    {constant : Constant} {type₁ type₂ : ClosedAnnotatedType}
    (first : PositiveTyping registry context₁ constant type₁)
    (second : PositiveTyping registry context₂ constant type₂) :
    type₁.erase = type₂.erase :=
  registry.sameErasure first.annotatedType second.annotatedType

/-- Every registered translation returns well-formed primed and witness terms. -/
theorem RegisteredTranslation.outputsWellFormed
    {registry : Registry Constant Output} {constant : Constant} {primed witness : Output}
    {type : ClosedAnnotatedType}
    (registered : RegisteredTranslation registry constant type primed witness) :
    registry.outputWellFormed primed ∧ registry.outputWellFormed witness :=
  registry.translationWellFormed registered

/-- A registered translation is indexed by a declared constant and an admissible annotated type. -/
theorem RegisteredTranslation.sourceValid
    {registry : Registry Constant Output} {constant : Constant} {primed witness : Output}
    {type : ClosedAnnotatedType}
    (registered : RegisteredTranslation registry constant type primed witness) :
    registry.declared constant ∧ registry.annotatedType constant type :=
  registry.translationSourceValid registered

/-- Every registered translation lookup induces the positive constant-typing rule. -/
theorem RegisteredTranslation.positiveTyping
    {registry : Registry Constant Output} {constant : Constant} {primed witness : Output}
    {type : ClosedAnnotatedType}
    (registered : RegisteredTranslation registry constant type primed witness)
    (context : Context n) :
    PositiveTyping registry context constant type :=
  .constant registered.sourceValid.1 registered.sourceValid.2

/-- Translation of a fixed constant at a fixed annotation is functional. -/
theorem RegisteredConstantTranslation.functional
    {registry : Registry Constant Output} {TranslationContext : Type v}
    {context : TranslationContext} {constant : Constant}
    {firstPrimed firstWitness secondPrimed secondWitness : Output}
    {type : ClosedAnnotatedType}
    (first : RegisteredConstantTranslation registry context constant type
      firstPrimed firstWitness)
    (second : RegisteredConstantTranslation registry context constant type
      secondPrimed secondWitness) :
    firstPrimed = secondPrimed ∧ firstWitness = secondWitness := by
  cases first with
  | registered firstEntry =>
      cases second with
      | registered secondEntry =>
          have pairEqual : (firstPrimed, firstWitness) = (secondPrimed, secondWitness) := by
            exact Option.some.inj (firstEntry.symm.trans secondEntry)
          exact Prod.mk.inj pairEqual

/-- A registered-constant translation exposes a valid positive typing for its source annotation. -/
theorem RegisteredConstantTranslation.sourceTyping
    {registry : Registry Constant Output} {TranslationContext : Type v}
    {translationContext : TranslationContext} {constant : Constant}
    {type : ClosedAnnotatedType} {primed witness : Output}
    (translation : RegisteredConstantTranslation registry translationContext
      constant type primed witness)
    (typingContext : Context n) :
    PositiveTyping registry typingContext constant type := by
  cases translation with
  | registered entry => exact entry.positiveTyping typingContext

/-- A registered-constant translation uses an annotation inhabiting an annotated universe. -/
theorem RegisteredConstantTranslation.typeWellTyped
    {registry : Registry Constant Output} {TranslationContext : Type v}
    {translationContext : TranslationContext} {constant : Constant}
    {type : ClosedAnnotatedType} {primed witness : Output}
    (translation : RegisteredConstantTranslation registry translationContext
      constant type primed witness) :
    IsAnnotatedType type :=
  (translation.sourceTyping Context.empty).typeWellTyped

/-- A missing registry lookup is equivalent to absence of a constant-translation derivation. -/
theorem isStuck_iff_no_registeredConstantTranslation
    {registry : Registry Constant Output} {TranslationContext : Type v}
    (context : TranslationContext) (constant : Constant) (type : ClosedAnnotatedType) :
    IsStuck registry constant type ↔
      ¬ ∃ primed witness,
        RegisteredConstantTranslation registry context constant type primed witness := by
  constructor
  · intro stuck derivation
    obtain ⟨primed, witness, derivation⟩ := derivation
    cases derivation with
    | registered entry =>
        rw [RegisteredTranslation, stuck] at entry
        contradiction
  · intro noDerivation
    cases lookup : registry.translation constant type with
    | none => exact lookup
    | some result =>
        obtain ⟨primed, witness⟩ := result
        exfalso
        exact noDerivation ⟨primed, witness, .registered lookup⟩

/-- Completeness supplies a registered translation for every positively typed constant. -/
theorem Registry.IsComplete.exists_registeredConstantTranslation
    {registry : Registry Constant Output} (complete : registry.IsComplete)
    {typingContext : Context n} {TranslationContext : Type v}
    (translationContext : TranslationContext) {constant : Constant}
    {type : ClosedAnnotatedType}
    (typing : PositiveTyping registry typingContext constant type) :
    ∃ primed witness,
      RegisteredConstantTranslation registry translationContext constant type primed witness := by
  obtain ⟨primed, witness, registered⟩ :=
    complete typing.declared typing.annotatedType
  exact ⟨primed, witness, .registered registered⟩

/-- In a complete registry, a stuck annotation cannot positively type the constant. -/
theorem IsStuck.not_positiveTyping_of_complete
    {registry : Registry Constant Output} (complete : registry.IsComplete)
    {constant : Constant} {type : ClosedAnnotatedType}
    (stuck : IsStuck registry constant type) (typingContext : Context n) :
    ¬ PositiveTyping registry typingContext constant type := by
  intro typing
  obtain ⟨primed, witness, translated⟩ :=
    complete.exists_registeredConstantTranslation Unit.unit typing
  exact (isStuck_iff_no_registeredConstantTranslation Unit.unit constant type).mp stuck
    ⟨primed, witness, translated⟩

/-- An undeclared constant has no derivation by the positive constant rule. -/
theorem not_positiveTyping_of_not_declared
    {registry : Registry Constant Output} {constant : Constant} {type : ClosedAnnotatedType}
    (notDeclared : ¬ registry.declared constant) (context : Context n) :
    ¬ PositiveTyping registry context constant type := by
  intro typing
  exact notDeclared typing.declared

/-- An unlisted annotated type has no derivation by the positive constant rule. -/
theorem not_positiveTyping_of_not_annotatedType
    {registry : Registry Constant Output} {constant : Constant} {type : ClosedAnnotatedType}
    (notAllowed : ¬ registry.annotatedType constant type) (context : Context n) :
    ¬ PositiveTyping registry context constant type := by
  intro typing
  exact notAllowed typing.annotatedType

example (registry : Registry Constant Output) {context : Context n}
    {constant : Constant} {type : ClosedAnnotatedType}
    (declared : registry.declared constant)
    (allowed : registry.annotatedType constant type) :
    PositiveTyping registry context constant type :=
  .constant declared allowed

example {registry : Registry Constant Output} {context : Context n}
    {constant : Constant} {type : ClosedAnnotatedType}
    (typing : PositiveTyping registry context constant type) :
    ∃ level annotation,
      HasType Context.empty type (.sort level annotation) :=
  typing.typeWellTyped

example (registry : Registry Constant Output) {TranslationContext : Type v}
    {context : TranslationContext} {constant : Constant} {primed witness : Output}
    {type : ClosedAnnotatedType}
    (lookup : registry.translation constant type = some (primed, witness)) :
    RegisteredConstantTranslation registry context constant type primed witness :=
  .registered lookup

example {registry : Registry Constant Output} {TranslationContext : Type v}
    {translationContext : TranslationContext} {constant : Constant}
    {type : ClosedAnnotatedType} {primed witness : Output}
    (translation : RegisteredConstantTranslation registry translationContext
      constant type primed witness) :
    IsAnnotatedType type :=
  translation.typeWellTyped

example (registry : Registry Constant Output) {TranslationContext : Type v}
    (context : TranslationContext) (constant : Constant) (type : ClosedAnnotatedType) :
    registry.translation constant type = none ↔
      ¬ ∃ primed witness,
        RegisteredConstantTranslation registry context constant type primed witness :=
  isStuck_iff_no_registeredConstantTranslation context constant type

example (registry : Registry Constant Output) (complete : registry.IsComplete)
    {typingContext : Context n} {TranslationContext : Type v}
    (translationContext : TranslationContext) {constant : Constant}
    {type : ClosedAnnotatedType}
    (typing : PositiveTyping registry typingContext constant type) :
    ∃ primed witness,
      RegisteredConstantTranslation registry translationContext constant type primed witness :=
  complete.exists_registeredConstantTranslation translationContext typing

end DeepWiki.Refine.RegisteredConstants
