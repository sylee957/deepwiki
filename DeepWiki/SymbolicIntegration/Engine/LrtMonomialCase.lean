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

/-- A semantic certificate for a rational special result in the root-free LRT path. -/
def IsLrtMonomialSpecialResult (Dt fp b ds snum sden : P α) : Prop :=
  CPoly.toPoly sden ≠ 0 ∧
    towerFractionFieldDerivP Dt (fieldFracP snum sden) =
      fieldFracP fp CPoly.one + fieldFracP b ds

/-- Denotational soundness contract for an LRT rational special-stage operation. -/
class LawfulCLrtMonomialCase (C : CLrtMonomialCase P α) : Prop where
  /-- Every returned fraction differentiates to the requested polynomial and special parts. -/
  special_sound : ∀ (Dt fp b ds snum sden : P α),
    C.integrateSpecial Dt fp b ds = some (snum, sden) →
      CPoly.toPoly sden ≠ 0 ∧
        towerFractionFieldDerivP Dt (fieldFracP snum sden) =
          fieldFracP fp CPoly.one + fieldFracP b ds

omit [LawfulCPolyEngine P] in
/-- A lawful LRT special-stage run yields its rational semantic result certificate. -/
theorem isLrtMonomialSpecialResult_of_run (C : CLrtMonomialCase P α)
    [LawfulCLrtMonomialCase C] (Dt fp b ds snum sden : P α)
    (hrun : C.integrateSpecial Dt fp b ds = some (snum, sden)) :
    IsLrtMonomialSpecialResult Dt fp b ds snum sden :=
  LawfulCLrtMonomialCase.special_sound Dt fp b ds snum sden hrun

/-- View an LRT rational special result as a generic integral result with no ordinary logarithms. -/
def lrtRationalSpecialResult (snum sden : P α) : IntegralResult α P :=
  ⟨(snum, sden), []⟩

omit [LawfulCPolyEngine P] in
/-- An LRT rational special certificate supplies the common monomial-special certificate without
encoding its separate algebraic-residue logarithms as ordinary logarithms. -/
theorem IsLrtMonomialSpecialResult.toIsMonomialSpecialResult
    {Dt fp b ds snum sden : P α}
    (h : IsLrtMonomialSpecialResult Dt fp b ds snum sden) :
    IsMonomialSpecialResult Dt fp b ds (lrtRationalSpecialResult snum sden) := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · simp [lrtRationalSpecialResult]
  · simp [lrtRationalSpecialResult]
  · simpa only [lrtRationalSpecialResult, logResidueSumP, List.map_nil, List.sum_nil, add_zero]
      using h.2

omit [LawfulCPolyEngine P] in
/-- A successful lawful LRT special stage supplies the common special witness used by one-level
assembly. -/
theorem lrtRationalSpecialResult_of_run (C : CLrtMonomialCase P α)
    [LawfulCLrtMonomialCase C] (Dt fp b ds snum sden : P α)
    (hrun : C.integrateSpecial Dt fp b ds = some (snum, sden)) :
    IsMonomialSpecialResult Dt fp b ds (lrtRationalSpecialResult snum sden) :=
  (isLrtMonomialSpecialResult_of_run C Dt fp b ds snum sden hrun).toIsMonomialSpecialResult

/-- Relative-completeness contract for an LRT rational special-stage operation. -/
class CompleteCLrtMonomialCase (C : CLrtMonomialCase P α)
    (domain : MonomialSpecialDomain P α) : Prop where
  /-- Every in-domain rational special antiderivative is accepted. -/
  special_complete : ∀ (Dt fp b ds snum sden : P α),
    domain Dt fp b ds → CPoly.toPoly sden ≠ 0 →
    towerFractionFieldDerivP Dt (fieldFracP snum sden) =
      fieldFracP fp CPoly.one + fieldFracP b ds →
    ∃ out, C.integrateSpecial Dt fp b ds = some out

omit [LawfulCPolyEngine P] in
/-- Relative completeness of an LRT rational special stage produces the common semantic special
witness, while leaving algebraic-residue logarithms at the LRT layer. -/
theorem lrtRationalSpecialResult_exists_of_complete (C : CLrtMonomialCase P α)
    (domain : MonomialSpecialDomain P α) [LawfulCLrtMonomialCase C]
    [CompleteCLrtMonomialCase C domain]
    (Dt fp b ds snum sden : P α) (hdomain : domain Dt fp b ds)
    (hsden : CPoly.toPoly sden ≠ 0)
    (hidentity : towerFractionFieldDerivP Dt (fieldFracP snum sden) =
      fieldFracP fp CPoly.one + fieldFracP b ds) :
    ∃ res : IntegralResult α P, IsMonomialSpecialResult Dt fp b ds res := by
  obtain ⟨out, hrun⟩ := CompleteCLrtMonomialCase.special_complete (C := C) Dt fp b ds snum sden
    hdomain hsden hidentity
  obtain ⟨outNum, outDen⟩ := out
  exact ⟨lrtRationalSpecialResult outNum outDen,
    lrtRationalSpecialResult_of_run C Dt fp b ds outNum outDen hrun⟩

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
