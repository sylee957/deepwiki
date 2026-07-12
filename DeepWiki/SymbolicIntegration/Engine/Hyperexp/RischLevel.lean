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

/-- Fully semantic hyperexponential level domain: polynomial-stage witnesses, semantic residual
normal reduction, and semantic Laurent special integration. -/
def hyperexpRischLevelSemanticCompleteDomain (R : CPolynomialReduction DensePoly α)
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    [CCanonicalRepresentation DensePoly α] : RischLevelDomain DensePoly α :=
  oneLevelRischCompleteDomain R kind polynomialDomain
    (hyperexpResidualNormalCompleteDomain (α := α))
    (hyperexpLaurentSpecialDomain (α := α))

/-- The fully semantic hyperexponential domain inherits soundness from the selected checked stages. -/
instance instLawfulCRischLevelHyperexpSemanticCompleteDomain (R : CPolynomialReduction DensePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulCRischLevel (hyperexpRischLevel (α := α) R kind)
      (hyperexpRischLevelSemanticCompleteDomain R kind polynomialDomain) := by
  unfold hyperexpRischLevel hyperexpRischLevelSemanticCompleteDomain
  infer_instance

/-- Field-RDE completeness composes every semantic hyperexponential stage into a relatively complete
one-level Risch solver. -/
theorem completeCRischLevelHyperexpSemantic (R : CPolynomialReduction DensePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    [CompleteCPolynomialReduction R polynomialDomain]
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)]
    [CRischFieldSpec α] (hfield : CRischFieldComplete α) :
    CompleteCRischLevel (hyperexpRischLevel (α := α) R kind)
      (hyperexpRischLevelSemanticCompleteDomain R kind polynomialDomain) := by
  letI : CompleteCNormalReduction (hyperexpCheckedNormalReduction (α := α))
      (hyperexpResidualNormalCompleteDomain (α := α)) :=
    completeCNormalReductionHyperexpSemantic hfield
  letI : CompleteCMonomialCase (DensePoly.hyperexpCheckedCase (α := α))
      (hyperexpLaurentSpecialDomain (α := α)) :=
    completeCMonomialCaseHyperexpLaurent hfield
  exact completeCRischLevel R kind polynomialDomain
    (hyperexpCheckedNormalReduction (α := α))
    (hyperexpResidualNormalCompleteDomain (α := α))
    (DensePoly.hyperexpCheckedCase (α := α))
    (hyperexpLaurentSpecialDomain (α := α))

end DeepWiki.SymbolicIntegration
