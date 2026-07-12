import DeepWiki.SymbolicIntegration.Engine.Hyperexp.CaseChecked
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.NormalCapability
import DeepWiki.SymbolicIntegration.Engine.RischLevel

/-! # Compositional hyperexponential Risch level

The checked hyperexponential special and normal stages are assembled through the generic one-level
Risch interface.
-/

namespace DeepWiki.SymbolicIntegration

universe u

variable {α : Type u} [CField α] [CFieldSpec.{u,u} α] [CDiffField α]
  [CDiffFieldSpec.{u,u} α] [CRischField α] [Algebra ℚ (CFieldSpec.K α)]
  [CPolyGcd DensePoly α] [CPolySquarefree DensePoly α]
  [CPolyResultant DensePoly] [CResidueSource DensePoly α]

/-- Dense hyperexponential Figure-5.1 level using checked special and residual-feedback normal stages. -/
def hyperexpRischLevel (R : CPolynomialReduction DensePoly α)
    (kind : PolynomialReductionKind) [CCanonicalRepresentation DensePoly α] :
    CRischLevel DensePoly α :=
  oneLevelRisch R kind (hyperexpCheckedNormalReduction (α := α))
    (DensePoly.hyperexpCheckedCase (α := α))

/-- Lawful dense stages compose into soundness of the hyperexponential Risch level. -/
instance instLawfulCRischLevelHyperexp (R : CPolynomialReduction DensePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulCRischLevel (hyperexpRischLevel (α := α) R kind)
      (oneLevelRischSoundDomain (hyperexpCheckedNormalDomain (α := α))) := by
  unfold hyperexpRischLevel
  infer_instance

/-- Exact composition domain of the checked hyperexponential Risch level. -/
def hyperexpRischLevelCompleteDomain (R : CPolynomialReduction DensePoly α)
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    [CCanonicalRepresentation DensePoly α] : RischLevelDomain DensePoly α :=
  oneLevelRischCompleteDomain R kind polynomialDomain
    (hyperexpCheckedNormalAcceptanceDomain (α := α))
    (hyperexpCheckedSpecialDomain (α := α))

/-- The checked hyperexponential level is lawful on its explicit stage-acceptance domain. -/
instance instLawfulCRischLevelHyperexpCompleteDomain (R : CPolynomialReduction DensePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulCRischLevel (hyperexpRischLevel (α := α) R kind)
      (hyperexpRischLevelCompleteDomain R kind polynomialDomain) := by
  unfold hyperexpRischLevel hyperexpRischLevelCompleteDomain
  infer_instance

/-- Complete checked stages compose to a relatively complete hyperexponential Risch level. -/
instance instCompleteCRischLevelHyperexp (R : CPolynomialReduction DensePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    [CompleteCPolynomialReduction R polynomialDomain]
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    CompleteCRischLevel (hyperexpRischLevel (α := α) R kind)
      (hyperexpRischLevelCompleteDomain R kind polynomialDomain) := by
  exact completeCRischLevel R kind polynomialDomain
    (hyperexpCheckedNormalReduction (α := α))
    (hyperexpCheckedNormalAcceptanceDomain (α := α))
    (DensePoly.hyperexpCheckedCase (α := α))
    (hyperexpCheckedSpecialDomain (α := α))

end DeepWiki.SymbolicIntegration
