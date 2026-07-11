import DeepWiki.SymbolicIntegration.Engine.Assemble
import DeepWiki.SymbolicIntegration.Engine.RecursiveCoefficient

/-! # Rational special-stage interfaces for root-free LRT integration

The LRT assembler has its own algebraic-residue log representation, so its monomial special stage returns
only a rational fraction. This interface keeps that restriction out of the generic Figure-5.1 assembler. -/

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Prop-free rational special-stage operation used by the root-free LRT assembler. -/
structure CLrtMonomialCase (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] where
  /-- Integrate the polynomial and special-denominator parts to a rational fraction. -/
  integrateSpecial : P α → P α → P α → P α → Option (P α × P α)

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Denotational soundness contract for an LRT rational special-stage operation. -/
class LawfulCLrtMonomialCase (C : CLrtMonomialCase P α) : Prop where
  /-- Every returned fraction differentiates to the requested polynomial and special parts. -/
  special_sound : ∀ (Dt fp b ds snum sden : P α),
    C.integrateSpecial Dt fp b ds = some (snum, sden) →
      CPoly.toPoly sden ≠ 0 ∧
        towerFractionFieldDerivP Dt (fieldFracP snum sden) =
          fieldFracP fp CPoly.one + fieldFracP b ds

/-- Relative-completeness contract for an LRT rational special-stage operation. -/
class CompleteCLrtMonomialCase (C : CLrtMonomialCase P α)
    (domain : MonomialSpecialDomain P α) : Prop where
  /-- Every in-domain rational special antiderivative is accepted. -/
  special_complete : ∀ (Dt fp b ds snum sden : P α),
    domain Dt fp b ds → CPoly.toPoly sden ≠ 0 →
    towerFractionFieldDerivP Dt (fieldFracP snum sden) =
      fieldFracP fp CPoly.one + fieldFracP b ds →
    ∃ out, C.integrateSpecial Dt fp b ds = some out

/-- Prop-free LRT special stage whose coefficient work is supplied recursively. -/
structure CRecursiveLrtMonomialCase (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] where
  /-- Integrate the rational special part using a recursive coefficient-field operation. -/
  integrateSpecial : CRecursiveCoefficientIntegrator α →
    P α → P α → P α → P α → Option (P α × P α)

/-- Install a selected recursive coefficient operation into an LRT special stage. -/
def CRecursiveLrtMonomialCase.withCoefficient (C : CRecursiveLrtMonomialCase P α)
    (I : CRecursiveCoefficientIntegrator α) : CLrtMonomialCase P α where
  integrateSpecial := C.integrateSpecial I

/-- Soundness contract for an LRT special stage before selecting its coefficient operation. -/
class LawfulCRecursiveLrtMonomialCase (C : CRecursiveLrtMonomialCase P α) : Prop where
  /-- Every lawful coefficient operation produces a lawful rational special stage. -/
  lawful : ∀ (I : CRecursiveCoefficientIntegrator α),
    LawfulCRecursiveCoefficientIntegrator I → LawfulCLrtMonomialCase (C.withCoefficient I)

/-- Install the recursive LRT special-stage soundness contract. -/
instance instLawfulCLrtMonomialCaseWithCoefficient (C : CRecursiveLrtMonomialCase P α)
    [LawfulCRecursiveLrtMonomialCase C] (I : CRecursiveCoefficientIntegrator α)
    [LawfulCRecursiveCoefficientIntegrator I] : LawfulCLrtMonomialCase (C.withCoefficient I) :=
  LawfulCRecursiveLrtMonomialCase.lawful I inferInstance

/-- Relative completeness contract before selecting recursive coefficient operations. -/
class CompleteCRecursiveLrtMonomialCase (C : CRecursiveLrtMonomialCase P α)
    (recursiveDomain : RecursiveCoefficientDomain (α := α))
    (limitedDomain : LimitedCoefficientDomain (α := α))
    (specialDomain : MonomialSpecialDomain P α) : Prop where
  /-- Complete coefficient operations make the installed rational special stage complete. -/
  complete (I : CRecursiveCoefficientIntegrator α)
    [CompleteCRecursiveCoefficientIntegrator I recursiveDomain]
    [LawfulCLimitedCoefficientIntegrator I]
    [CompleteCLimitedCoefficientIntegrator I limitedDomain] :
      CompleteCLrtMonomialCase (C.withCoefficient I) specialDomain

omit [LawfulCPolyEngine P] in
/-- Install recursive coefficient completeness into an LRT rational special stage. -/
theorem completeCLrtMonomialCaseWithRecursiveCoefficient (C : CRecursiveLrtMonomialCase P α)
    (recursiveDomain : RecursiveCoefficientDomain (α := α))
    (limitedDomain : LimitedCoefficientDomain (α := α))
    (specialDomain : MonomialSpecialDomain P α)
    [CompleteCRecursiveLrtMonomialCase C recursiveDomain limitedDomain specialDomain]
    (I : CRecursiveCoefficientIntegrator α)
    [CompleteCRecursiveCoefficientIntegrator I recursiveDomain]
    [LawfulCLimitedCoefficientIntegrator I]
    [CompleteCLimitedCoefficientIntegrator I limitedDomain] :
    CompleteCLrtMonomialCase (C.withCoefficient I) specialDomain :=
  CompleteCRecursiveLrtMonomialCase.complete (C := C) (recursiveDomain := recursiveDomain)
    (limitedDomain := limitedDomain) (specialDomain := specialDomain) I

end DeepWiki.SymbolicIntegration
