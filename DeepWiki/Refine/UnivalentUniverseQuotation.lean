import DeepWiki.Refine.RawParametricityTyping

/-! # Quoting univalent universe packages

The scoped dependent calculus exposes an explicit boundary for adding closed univalent universe
packages and a relation projection with its object-language typing and conversion laws.
-/

namespace DeepWiki.Refine.DependentCalculus

/-- A typing judgment on the existing intrinsically scoped object language. -/
abbrev TypingJudgment := {n : Nat} → Context n → Term n → Term n → Prop

/-- A definitional-conversion judgment on the existing intrinsically scoped object language. -/
abbrev ConversionJudgment := {n : Nat} → Term n → Term n → Prop

/-- An extension of ordinary typing and conversion that retains application and type conversion. -/
structure ObjectCalculusExtension where
  /-- The extended object-language typing judgment. -/
  hasType : TypingJudgment
  /-- The extended object-language definitional-conversion judgment. -/
  convertible : ConversionJudgment
  /-- Every ordinary typing derivation remains valid in the extension. -/
  ofHasType : ∀ {n : Nat} {context : Context n} {term type : Term n},
    HasType context term type → hasType context term type
  /-- Every ordinary definitional conversion remains valid in the extension. -/
  ofConvertible : ∀ {n : Nat} {left right : Term n},
    Convertible left right → convertible left right
  /-- Extended typing is closed under dependent application. -/
  app : ∀ {n : Nat} {context : Context n} {function argument domain : Term n}
      {codomain : Term (n + 1)},
    hasType context function (.pi domain codomain) →
      hasType context argument domain →
        hasType context (.app function argument) (codomain.instantiate argument)
  /-- Extended typing permits conversion to a well-formed definitionally equal type. -/
  conversion : ∀ {n : Nat} {context : Context n} {term type type' : Term n} {level : Nat},
    hasType context term type →
      hasType context type' (.sort level) →
        convertible type type' →
          hasType context term type'

/-- Ordinary dependent typing and beta conversion form the identity object-calculus extension. -/
def ObjectCalculusExtension.core : ObjectCalculusExtension where
  hasType := HasType
  convertible := Convertible
  ofHasType := id
  ofConvertible := id
  app := HasType.app
  conversion := HasType.conversion

/-- The object-language type of a binary relation between two inhabitants of a universe. -/
def universeRelationFamilyType (level : Nat) : Term 0 :=
  RawParametricity.sortRelationType level 0

/-- The required type of a quoted universe package at one object-language universe level. -/
def quotedUniversePackageType (typeTranslation : Nat → Term 0) (level : Nat) : Term 0 :=
  .app (.app (typeTranslation (level + 1)) (.sort level)) (.sort level)

/-- The type of a projection extracting the relation family from a quoted universe package. -/
def universeRelationProjectionType (typeTranslation : Nat → Term 0)
    (level : Nat) : Term 0 :=
  .pi (quotedUniversePackageType typeTranslation level)
    ((universeRelationFamilyType level).rename Renaming.shift)

/-- Closed object-language data satisfying universe-package typing and relation-projection laws. -/
structure UnivalentUniverseQuotation (calculus : ObjectCalculusExtension) where
  /-- The relation-valued translation of every object-language universe. -/
  typeTranslation : Nat → Term 0
  /-- The package-valued term translation of every object-language universe. -/
  termTranslation : Nat → Term 0
  /-- A level-indexed object-language projection from packages to relation families. -/
  relationProjection : Nat → Term 0
  /-- Every translated universe relation has the expected binary-relation type. -/
  typeTranslation_hasType : ∀ level,
    calculus.hasType Context.empty (typeTranslation level)
      (universeRelationFamilyType level)
  /-- Every translated universe package inhabits the next relation at two copies of its universe. -/
  termTranslation_hasType : ∀ level,
    calculus.hasType Context.empty (termTranslation level)
      (quotedUniversePackageType typeTranslation level)
  /-- Every relation projection maps a universe package to its binary relation family. -/
  relationProjection_hasType : ∀ level,
    calculus.hasType Context.empty (relationProjection level)
      (universeRelationProjectionType typeTranslation level)
  /-- Projecting a translated universe package definitionally yields its type translation. -/
  relationProjection_beta : ∀ level,
    calculus.convertible
      (.app (relationProjection level) (termTranslation level))
      (typeTranslation level)

namespace UnivalentUniverseQuotation

/-- Apply the quoted relation projection to the package-valued universe translation. -/
def projectedRelation {calculus : ObjectCalculusExtension}
    (quotation : UnivalentUniverseQuotation calculus) (level : Nat) : Term 0 :=
  .app (quotation.relationProjection level) (quotation.termTranslation level)

/-- The projected relation is well typed as a binary relation family. -/
theorem projectedRelation_hasType {calculus : ObjectCalculusExtension}
    (quotation : UnivalentUniverseQuotation calculus) (level : Nat) :
    calculus.hasType Context.empty (quotation.projectedRelation level)
      (universeRelationFamilyType level) := by
  have application := calculus.app (quotation.relationProjection_hasType level)
    (quotation.termTranslation_hasType level)
  simpa only [projectedRelation, universeRelationProjectionType,
    Term.instantiate_rename_shift] using application

/-- The projected relation definitionally converts to the relation-valued universe translation. -/
theorem projectedRelation_convertible {calculus : ObjectCalculusExtension}
    (quotation : UnivalentUniverseQuotation calculus) (level : Nat) :
    calculus.convertible (quotation.projectedRelation level)
      (quotation.typeTranslation level) :=
  quotation.relationProjection_beta level

end UnivalentUniverseQuotation

/-- Realizability of univalent universe quotation inside the unextended dependent calculus. -/
def CoreUnivalentUniverseQuotationRealizability : Prop :=
  Nonempty (UnivalentUniverseQuotation ObjectCalculusExtension.core)

example {calculus : ObjectCalculusExtension}
    (quotation : UnivalentUniverseQuotation calculus) (level : Nat) :
    calculus.hasType Context.empty (quotation.termTranslation level)
      (.app (.app (quotation.typeTranslation (level + 1)) (.sort level)) (.sort level)) :=
  quotation.termTranslation_hasType level

example {calculus : ObjectCalculusExtension}
    (quotation : UnivalentUniverseQuotation calculus) (level : Nat) :
    calculus.convertible
      (.app (quotation.relationProjection level) (quotation.termTranslation level))
      (quotation.typeTranslation level) :=
  quotation.projectedRelation_convertible level

end DeepWiki.Refine.DependentCalculus
