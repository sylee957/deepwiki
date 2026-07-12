import DeepWiki.ComputableAlgebra.PolyReprConvert
import DeepWiki.SymbolicIntegration.Engine.ResidueLogPartDense

/-! # Sparse residue-logarithm realization

The sparse-facing operation transports inputs and logarithm arguments across the checked dense backend. -/

namespace DeepWiki.SymbolicIntegration

open CFrac Polynomial

universe u v

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
  [Algebra ℚ (CFieldSpec.K α)] [CPolyGcd DensePoly α] [CPolyResultant DensePoly]
  [CResidueSource CPoly.SparsePoly α]

/-- View a sparse residue source as a dense source through denotation-preserving conversion. -/
@[reducible] private def denseResidueSourceFromSparse : CResidueSource DensePoly α where
  candidates R := CResidueSource.candidates (CPolyEngine.convert R : CPoly.SparsePoly α)

/-- Convert dense logarithm arguments to sparse representation without changing their coefficients. -/
private def sparseLogs (logs : List (α × DensePoly α)) : List (α × CPoly.SparsePoly α) :=
  logs.map fun cv => (cv.1, CPolyEngine.convert cv.2)

private def sparseResidueLogCompute (Dt hNum Dstar : CPoly.SparsePoly α) :
    Option (List (α × CPoly.SparsePoly α)) :=
  letI : CResidueSource DensePoly α := denseResidueSourceFromSparse
  let denseDt : DensePoly α := CPolyEngine.convert Dt
  let denseNum : DensePoly α := CPolyEngine.convert hNum
  let denseDen : DensePoly α := CPolyEngine.convert Dstar
  (DensePoly.checkedResidueLogPart denseDt denseNum denseDen).map sparseLogs

/-- Sparse checked residue-logarithm extraction through a dense backend. -/
instance instCResidueLogPartSparse : CResidueLogPart CPoly.SparsePoly α where
  compute := sparseResidueLogCompute

/-- The sparse checked residue-logarithm operation satisfies the representation-neutral soundness contract. -/
instance instLawfulCResidueLogPartSparse :
    LawfulCResidueLogPart (P := CPoly.SparsePoly) (α := α) where
  sound Dt hNum Dstar logs hrun := by
    letI : CResidueSource DensePoly α := denseResidueSourceFromSparse
    let denseDt : DensePoly α := CPolyEngine.convert Dt
    let denseNum : DensePoly α := CPolyEngine.convert hNum
    let denseDen : DensePoly α := CPolyEngine.convert Dstar
    change sparseResidueLogCompute Dt hNum Dstar = some logs at hrun
    change (DensePoly.checkedResidueLogPart denseDt denseNum denseDen).map sparseLogs = some logs at hrun
    rw [Option.map_eq_some_iff] at hrun
    obtain ⟨denseLogs, hdense, rfl⟩ := hrun
    have h := instLawfulCResidueLogPartDense.sound denseDt denseNum denseDen denseLogs hdense
    refine ⟨?_⟩
    let sparseTerm := fun cv : α × CPoly.SparsePoly α =>
      am α (Polynomial.C (CFieldSpec.toK cv.1)) *
        (towerFractionFieldDerivP Dt (am α (CPoly.toPoly cv.2)) / am α (CPoly.toPoly cv.2))
    let denseTerm := fun cv : α × DensePoly α =>
      am α (Polynomial.C (CFieldSpec.toK cv.1)) *
        (towerFractionFieldDerivP denseDt (am α (CPoly.toPoly cv.2)) / am α (CPoly.toPoly cv.2))
    change ((sparseLogs denseLogs).map sparseTerm).sum =
      am α (CPoly.toPoly hNum) / am α (CPoly.toPoly Dstar)
    have hmap : (sparseLogs denseLogs).map sparseTerm = denseLogs.map denseTerm := by
      rw [sparseLogs, List.map_map]
      apply List.map_congr_left
      intro cv _
      simp only [Function.comp_apply, sparseTerm, denseTerm, towerFractionFieldDerivP, denseDt,
        CPolyEngine.toPoly_convert]
    rw [hmap]
    simpa only [denseTerm, denseDt, denseNum, denseDen, CPolyEngine.toPoly_convert]
      using h.residue_match

/-- Exact executable acceptance domain of sparse checked residue extraction. -/
def sparseResidueLogPartAcceptanceDomain :
    ResidueLogPartDomain (P := CPoly.SparsePoly) (α := α) := fun Dt hNum Dstar =>
  ∃ logs : List (α × CPoly.SparsePoly α),
    CResidueLogPart.compute Dt hNum Dstar = some logs ∧ GenuineResidueLogPart Dt hNum Dstar logs

/-- Sparse checked residue extraction is relatively complete on its explicit acceptance domain. -/
instance instCompleteCResidueLogPartSparseCheckedAcceptance :
    CompleteCResidueLogPart (P := CPoly.SparsePoly) (α := α)
      sparseResidueLogPartAcceptanceDomain where
  complete _ _ _ _ hdomain _ _ _ _ := hdomain

end DeepWiki.SymbolicIntegration
