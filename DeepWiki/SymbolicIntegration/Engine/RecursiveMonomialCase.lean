import DeepWiki.SymbolicIntegration.Engine.Assemble
import DeepWiki.SymbolicIntegration.Engine.RecursiveCoefficient

/-! # Recursive coefficient stage for monomial cases

A tower monomial case consumes an immediately lower coefficient-field integrator.  This module
makes that dependency an executable, representation-neutral stage instead of hiding it inside a
concrete special solver. -/

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Prop-free monomial-case operation parameterized by recursive coefficient integration. -/
structure CRecursiveMonomialCase (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] where
  /-- Integrate the special part using the supplied lower-field coefficient integrator. -/
  integrateSpecial : CRecursiveCoefficientIntegrator α →
    P α → P α → P α → P α → Option (P α × P α)
  /-- Post-process the normal result after the recursive special stage. -/
  postprocessNormal : P α → IntegralResult α P → Option (IntegralResult α P)

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Fix the recursive coefficient integrator to obtain the ordinary monomial-case stage consumed by
the generic Figure-5.1 assembler. -/
def CRecursiveMonomialCase.withCoefficient (C : CRecursiveMonomialCase P α)
    (I : CRecursiveCoefficientIntegrator α) : CMonomialCase P α where
  integrateSpecial := C.integrateSpecial I
  postprocessNormal := C.postprocessNormal

/-- Soundness contract for a recursive monomial case: every lawful lower-field integrator induces a
lawful ordinary monomial case. -/
class LawfulCRecursiveMonomialCase (C : CRecursiveMonomialCase P α) : Prop where
  /-- Installing a sound recursive coefficient stage preserves monomial-case soundness. -/
  lawful : ∀ (I : CRecursiveCoefficientIntegrator α),
    LawfulCRecursiveCoefficientIntegrator I → LawfulCMonomialCase (C.withCoefficient I)

/-- A lawful recursive coefficient stage lifts to a lawful ordinary monomial case. -/
instance instLawfulCMonomialCaseWithRecursiveCoefficient (C : CRecursiveMonomialCase P α)
    (I : CRecursiveCoefficientIntegrator α) [LawfulCRecursiveMonomialCase C]
    [LawfulCRecursiveCoefficientIntegrator I] : LawfulCMonomialCase (C.withCoefficient I) :=
  LawfulCRecursiveMonomialCase.lawful (C := C) I inferInstance

/-- Relative-completeness contract for a recursive monomial case on selected coefficient domains. -/
class CompleteCRecursiveMonomialCase (C : CRecursiveMonomialCase P α)
    (recursiveDomain : RecursiveCoefficientDomain (α := α))
    (limitedDomain : LimitedCoefficientDomain (α := α))
    (specialDomain : MonomialSpecialDomain P α) : Prop where
  /-- Installing coefficient stages complete on the selected domains preserves monomial completeness. -/
  complete (I : CRecursiveCoefficientIntegrator α)
    [CompleteCRecursiveCoefficientIntegrator I recursiveDomain]
    [LawfulCLimitedCoefficientIntegrator I]
    [CompleteCLimitedCoefficientIntegrator I limitedDomain] :
      CompleteCMonomialCase (C.withCoefficient I) specialDomain

omit [LawfulCPolyEngine P] in
/-- Complete recursive coefficient stages lift to a complete ordinary monomial case on their named domains. -/
theorem completeCMonomialCaseWithRecursiveCoefficient (C : CRecursiveMonomialCase P α)
    (recursiveDomain : RecursiveCoefficientDomain (α := α))
    (limitedDomain : LimitedCoefficientDomain (α := α))
    (specialDomain : MonomialSpecialDomain P α)
    (I : CRecursiveCoefficientIntegrator α)
    [CompleteCRecursiveMonomialCase C recursiveDomain limitedDomain specialDomain]
    [CompleteCRecursiveCoefficientIntegrator I recursiveDomain]
    [LawfulCLimitedCoefficientIntegrator I]
    [CompleteCLimitedCoefficientIntegrator I limitedDomain] :
    CompleteCMonomialCase (C.withCoefficient I) specialDomain :=
  CompleteCRecursiveMonomialCase.complete (C := C) (recursiveDomain := recursiveDomain)
    (limitedDomain := limitedDomain) (specialDomain := specialDomain) I

end DeepWiki.SymbolicIntegration
