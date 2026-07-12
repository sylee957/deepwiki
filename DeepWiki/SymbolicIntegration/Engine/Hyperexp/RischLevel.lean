import DeepWiki.SymbolicIntegration.Engine.Hyperexp.CaseChecked
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.NormalCapability
import DeepWiki.SymbolicIntegration.Engine.RischLevel
import DeepWiki.SymbolicIntegration.Engine.RischLevelConvert

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

/-- The semantic hyperexponential level returns only genuine logarithmic reconstruction data. -/
instance instLawfulGenuineCRischLevelHyperexpSemanticCompleteDomain
    (R : CPolynomialReduction DensePoly α) [LawfulCPolynomialReduction R]
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulGenuineCRischLevel (hyperexpRischLevel (α := α) R kind)
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

/-- Sparse hyperexponential Risch level obtained solely by converting the dense semantic level. -/
def sparseHyperexpRischLevel (R : CPolynomialReduction DensePoly α)
    (kind : PolynomialReductionKind) [CCanonicalRepresentation DensePoly α] :
    CRischLevel CPoly.SparsePoly α :=
  convertRischLevel (Q := CPoly.SparsePoly) (hyperexpRischLevel (α := α) R kind)

/-- Sparse semantic domain obtained by pulling back the dense hyperexponential level domain. -/
def sparseHyperexpRischLevelSemanticCompleteDomain (R : CPolynomialReduction DensePoly α)
    (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    [CCanonicalRepresentation DensePoly α] : RischLevelDomain CPoly.SparsePoly α :=
  convertRischLevelDomain (Q := CPoly.SparsePoly)
    (hyperexpRischLevelSemanticCompleteDomain R kind polynomialDomain)

/-- Dense semantic soundness transports to the sparse hyperexponential level. -/
instance instLawfulCRischLevelSparseHyperexpSemantic (R : CPolynomialReduction DensePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)] :
    LawfulCRischLevel (sparseHyperexpRischLevel (α := α) R kind)
      (sparseHyperexpRischLevelSemanticCompleteDomain R kind polynomialDomain) := by
  unfold sparseHyperexpRischLevel sparseHyperexpRischLevelSemanticCompleteDomain
  infer_instance

/-- Dense semantic relative completeness transports to sparse hyperexponential representation. -/
theorem completeCRischLevelSparseHyperexpSemantic (R : CPolynomialReduction DensePoly α)
    [LawfulCPolynomialReduction R] (kind : PolynomialReductionKind)
    (polynomialDomain : PolynomialReductionDomain DensePoly α)
    [CompleteCPolynomialReduction R polynomialDomain]
    [CCanonicalRepresentation DensePoly α]
    [LawfulCCanonicalRepresentation (P := DensePoly) (α := α)]
    [CRischFieldSpec α] (hfield : CRischFieldComplete α) :
    CompleteCRischLevel (sparseHyperexpRischLevel (α := α) R kind)
      (sparseHyperexpRischLevelSemanticCompleteDomain R kind polynomialDomain) := by
  letI : CompleteCRischLevel (hyperexpRischLevel (α := α) R kind)
      (hyperexpRischLevelSemanticCompleteDomain R kind polynomialDomain) :=
    completeCRischLevelHyperexpSemantic R kind polynomialDomain hfield
  unfold sparseHyperexpRischLevel sparseHyperexpRischLevelSemanticCompleteDomain
  infer_instance

end DeepWiki.SymbolicIntegration
