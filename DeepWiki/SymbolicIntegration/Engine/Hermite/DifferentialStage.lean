import DeepWiki.SymbolicIntegration.Engine.Hermite.Reduction

/-! # Explicit-differential Hermite stage interface

The legacy Hermite interface obtains coefficient differentiation from `[CDiffField α]`. This
parallel interface records the computable and semantic derivations as data, so normality and the
Hermite reconstruction identity use the same selected differential in a mixed tower.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CFrac

universe u v

/-- The explicit differential data used by one monomial integration stage. -/
structure MonomialDifferentialContext {P : Type u → Type u} [CPoly P]
    (α : Type u) [CField α] [CFieldSpec.{u,v} α] where
  /-- Computable coefficient derivative. -/
  derivation : CFieldDerivation α
  /-- Mathematical coefficient-field differential. -/
  differential : Differential (CFieldSpec.K α)
  /-- Denotational law for the computable coefficient derivative. -/
  lawful : LawfulCFieldDerivation α derivation differential
  /-- Rational scalar algebra required by the rational-function extension. -/
  algebraQ : Algebra ℚ (CFieldSpec.K α)

namespace MonomialDifferentialContext

/-- The polynomial differential induced by the selected coefficient differential and monomial derivative. -/
@[reducible] noncomputable def polynomialDifferential {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (C : MonomialDifferentialContext (P := P) α) (Dt : P α) :
    Differential (CFieldSpec.K α)[X] := by
  letI : Differential (CRingSpec.R α) := C.differential
  exact ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩

/-- The function-field derivative induced by the selected coefficient differential and monomial derivative. -/
@[reducible] noncomputable def fractionDifferential {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (C : MonomialDifferentialContext (P := P) α) (Dt : P α) :
    Differential (RatFunc (CFieldSpec.K α)) := by
  letI : Differential (CRingSpec.R α) := C.differential
  letI : Algebra ℚ (CRingSpec.R α) := by
    change Algebra ℚ (CFieldSpec.K α)
    exact C.algebraQ
  exact fractionFieldDifferential (Differential.implicitDeriv (CPoly.toPoly Dt))

/-- The selected quotient-rule derivation on the monomial function field. -/
noncomputable def fractionDeriv {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (C : MonomialDifferentialContext (P := P) α) (Dt : P α) :
    Derivation ℤ (RatFunc (CFieldSpec.K α)) (RatFunc (CFieldSpec.K α)) :=
  by
    letI : Differential (CRingSpec.R α) := C.differential
    letI : Algebra ℚ (CRingSpec.R α) := by
      change Algebra ℚ (CFieldSpec.K α)
      exact C.algebraQ
    exact extendDeriv (Differential.implicitDeriv (CPoly.toPoly Dt))

end MonomialDifferentialContext

/-- A Hermite operation selected for one explicit coefficient derivation. -/
class CDifferentialHermiteReduction (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] (derivation : CFieldDerivation α) where
  /-- Extract a rational derivative and a squarefree-denominator remainder. -/
  compute : P α → P α → P α → HermiteReductionResult P α

/-- The result selected by an explicit-differential Hermite operation. -/
abbrev differentialHermiteResult {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (derivation : CFieldDerivation α)
    [CDifferentialHermiteReduction P α derivation] (Dt a d : P α) : HermiteReductionResult P α :=
  CDifferentialHermiteReduction.compute derivation Dt a d

/-- Semantic laws for an explicit-differential Hermite operation. -/
class LawfulCDifferentialHermiteReduction {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (C : MonomialDifferentialContext (P := P) α)
    [CDifferentialHermiteReduction P α C.derivation] : Prop where
  /-- The rational-part denominator is nonzero on a normal-squarefree input denominator. -/
  rationalDen_nonzero : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    @IsNormalSqfree _ _ (C.polynomialDifferential Dt) (CPoly.toPoly d) →
    CPoly.toPoly (differentialHermiteResult C.derivation Dt a d).rationalDen ≠ 0
  /-- The squarefree-remainder denominator is nonzero on a nonzero input denominator. -/
  remainderDen_nonzero : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    CPoly.toPoly (differentialHermiteResult C.derivation Dt a d).remainderDen ≠ 0
  /-- Hermite reduction reconstructs the input under the selected function-field derivative. -/
  field_identity : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    @IsNormalSqfree _ _ (C.polynomialDifferential Dt) (CPoly.toPoly d) →
    C.fractionDeriv Dt
        (am α (CPoly.toPoly (differentialHermiteResult C.derivation Dt a d).rationalNum) /
          am α (CPoly.toPoly (differentialHermiteResult C.derivation Dt a d).rationalDen))
      + am α (CPoly.toPoly (differentialHermiteResult C.derivation Dt a d).remainderNum) /
          am α (CPoly.toPoly (differentialHermiteResult C.derivation Dt a d).remainderDen)
      = am α (CPoly.toPoly a) / am α (CPoly.toPoly d)
  /-- The selected remainder denominator is squarefree. -/
  remainder_squarefree : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    Squarefree (CPoly.toPoly (differentialHermiteResult C.derivation Dt a d).remainderDen)
  /-- The selected remainder is proper under the standard degree hypothesis. -/
  remainder_proper : ∀ (Dt a d : P α), CPoly.toPoly d ≠ 0 →
    @IsNormalSqfree _ _ (C.polynomialDifferential Dt) (CPoly.toPoly d) →
    (CPoly.toPoly a).degree < (CPoly.toPoly d).degree →
    (CPoly.toPoly Dt).natDegree ≤ 1 →
    (CPoly.toPoly (differentialHermiteResult C.derivation Dt a d).remainderNum).degree <
      (CPoly.toPoly (differentialHermiteResult C.derivation Dt a d).remainderDen).degree

end DeepWiki.SymbolicIntegration
