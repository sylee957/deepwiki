import DeepWiki.SymbolicIntegration.Engine.CanonicalRepresentationSparse
import DeepWiki.SymbolicIntegration.Engine.Hermite.ReductionSparse
import DeepWiki.SymbolicIntegration.Engine.MonomialCaseSparse
import DeepWiki.SymbolicIntegration.Engine.ResidueLogPartSparse
import DeepWiki.SymbolicIntegration.Engine.RischLevel

/-! # Sparse realization of the compositional Risch level

The sparse-facing level composes transported stage realizations with the generic contract-based assembler. -/

namespace DeepWiki.SymbolicIntegration

universe u

variable {α : Type u} [CField α] [CFieldSpec.{u,u} α] [CDiffField α] [CDiffFieldSpec.{u,u} α]
  [CRischField α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
  [CFracGcdCoreWf α] [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))]
  [CPolyGcd DensePoly α] [LawfulCPolyGcd.{u,u} DensePoly α]
  [CPolySplitFactor DensePoly α] [LawfulCPolySplitFactor DensePoly α]
  [CPolyResultant DensePoly] [CResidueSource CPoly.SparsePoly α]

/-- Sparse Hermite-residue realization of the normal-reduction operation. -/
def sparseNormalReduction : CNormalReduction CPoly.SparsePoly α :=
  hermiteResidueNormalReduction

/-- Semantic domain of sparse Hermite-residue normal reduction. -/
def sparseNormalDomain : NormalReductionDomain CPoly.SparsePoly α :=
  hermiteResidueNormalSoundDomain

/-- Sparse Hermite-residue normal reduction satisfies its soundness contract. -/
instance instLawfulCNormalReductionSparse :
    LawfulCNormalReduction (sparseNormalReduction (α := α))
      (sparseNormalDomain (α := α)) := by
  unfold sparseNormalReduction sparseNormalDomain
  infer_instance

/-- Sparse Figure-5.1 level using a selected dense monomial-case specialization. -/
def sparseRischLevel (kind : PolynomialReductionKind) (C : CMonomialCase DensePoly α) :
    CRischLevel CPoly.SparsePoly α :=
  oneLevelRisch
    (DensePoly.towerPolynomialReduction (P := CPoly.SparsePoly) (α := α)) kind
    sparseNormalReduction
    (denseMonomialCaseAsSparse C)

/-- Lawful stage contracts compose into soundness of the sparse Figure-5.1 level. -/
instance instLawfulCRischLevelSparse (kind : PolynomialReductionKind)
    (C : CMonomialCase DensePoly α) [LawfulCMonomialCase C] :
    LawfulCRischLevel (sparseRischLevel kind C)
      (oneLevelRischSoundDomain sparseNormalDomain) := by
  unfold sparseRischLevel
  infer_instance

end DeepWiki.SymbolicIntegration
