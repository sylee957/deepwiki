import DeepWiki.ComputableAlgebra.PolyReprConvert
import DeepWiki.SymbolicIntegration.Engine.Hermite.ReductionDenseLawful

/-! # Sparse transcendental Hermite reduction

The sparse-facing realization transports the lawful dense reducer through polynomial conversion. -/

namespace DeepWiki.SymbolicIntegration

open CFrac Polynomial

universe u v

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

private def sparseHermiteCompute (Dt a d : CPoly.SparsePoly α) :
    HermiteReductionResult CPoly.SparsePoly α :=
  let denseDt : DensePoly α := CPolyEngine.convert Dt
  let denseA : DensePoly α := CPolyEngine.convert a
  let denseD : DensePoly α := CPolyEngine.convert d
  let out := hermiteResult denseDt denseA denseD
  { rationalNum := CPolyEngine.convert out.rationalNum
    rationalDen := CPolyEngine.convert out.rationalDen
    remainderNum := CPolyEngine.convert out.remainderNum
    remainderDen := CPolyEngine.convert out.remainderDen }

/-- Sparse Hermite reduction through a denotation-preserving dense backend. -/
instance instCHermiteReductionSparse : CHermiteReduction CPoly.SparsePoly α where
  compute := sparseHermiteCompute

omit [CFieldSpec α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]
    [CharZero (CFieldSpec.K α)] in
/-- The selected sparse Hermite result unfolds to the transported dense result. -/
private theorem hermiteResult_sparse_eq (Dt a d : CPoly.SparsePoly α) :
    hermiteResult Dt a d = sparseHermiteCompute Dt a d := rfl

/-- The sparse Hermite realization satisfies the representation-neutral semantic contract. -/
instance instLawfulCHermiteReductionSparse
    [Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))] :
    LawfulCHermiteReduction (P := CPoly.SparsePoly) (α := α) where
  rationalDen_nonzero Dt a d hd hnormal := by
    let denseDt : DensePoly α := CPolyEngine.convert Dt
    let denseA : DensePoly α := CPolyEngine.convert a
    let denseD : DensePoly α := CPolyEngine.convert d
    have hDt : CPoly.toPoly denseDt = CPoly.toPoly Dt := CPolyEngine.toPoly_convert Dt
    have hdense : CPoly.toPoly denseD ≠ 0 := by
      simpa only [denseD, CPolyEngine.toPoly_convert] using hd
    have hnormalDense :
        @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly denseDt)⟩
          (CPoly.toPoly denseD) := by
      rw [hDt]
      simpa only [denseD, CPolyEngine.toPoly_convert] using hnormal
    have h := instLawfulCHermiteReductionDenseWf.rationalDen_nonzero
      denseDt denseA denseD hdense hnormalDense
    simpa only [hermiteResult_sparse_eq, sparseHermiteCompute, denseDt, denseA, denseD,
      CPolyEngine.toPoly_convert] using h
  remainderDen_nonzero Dt a d hd := by
    let denseDt : DensePoly α := CPolyEngine.convert Dt
    let denseA : DensePoly α := CPolyEngine.convert a
    let denseD : DensePoly α := CPolyEngine.convert d
    have hdense : CPoly.toPoly denseD ≠ 0 := by
      simpa only [denseD, CPolyEngine.toPoly_convert] using hd
    have h := instLawfulCHermiteReductionDenseWf.remainderDen_nonzero
      denseDt denseA denseD hdense
    simpa only [hermiteResult_sparse_eq, sparseHermiteCompute, denseDt, denseA, denseD,
      CPolyEngine.toPoly_convert] using h
  field_identity Dt a d hd hnormal := by
    let denseDt : DensePoly α := CPolyEngine.convert Dt
    let denseA : DensePoly α := CPolyEngine.convert a
    let denseD : DensePoly α := CPolyEngine.convert d
    have hDt : CPoly.toPoly denseDt = CPoly.toPoly Dt := CPolyEngine.toPoly_convert Dt
    have hdense : CPoly.toPoly denseD ≠ 0 := by
      simpa only [denseD, CPolyEngine.toPoly_convert] using hd
    have hnormalDense :
        @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly denseDt)⟩
          (CPoly.toPoly denseD) := by
      rw [hDt]
      simpa only [denseD, CPolyEngine.toPoly_convert] using hnormal
    have h := instLawfulCHermiteReductionDenseWf.field_identity
      denseDt denseA denseD hdense hnormalDense
    simpa only [hermiteResult_sparse_eq, sparseHermiteCompute, denseDt, denseA, denseD,
      towerFractionFieldDerivP, CPolyEngine.toPoly_convert] using h
  remainder_squarefree Dt a d hd := by
    let denseDt : DensePoly α := CPolyEngine.convert Dt
    let denseA : DensePoly α := CPolyEngine.convert a
    let denseD : DensePoly α := CPolyEngine.convert d
    have hdense : CPoly.toPoly denseD ≠ 0 := by
      simpa only [denseD, CPolyEngine.toPoly_convert] using hd
    have h := instLawfulCHermiteReductionDenseWf.remainder_squarefree
      denseDt denseA denseD hdense
    simpa only [hermiteResult_sparse_eq, sparseHermiteCompute, denseDt, denseA, denseD,
      CPolyEngine.toPoly_convert] using h
  remainder_proper Dt a d hd hnormal hproper hdegree := by
    let denseDt : DensePoly α := CPolyEngine.convert Dt
    let denseA : DensePoly α := CPolyEngine.convert a
    let denseD : DensePoly α := CPolyEngine.convert d
    have hDt : CPoly.toPoly denseDt = CPoly.toPoly Dt := CPolyEngine.toPoly_convert Dt
    have hdense : CPoly.toPoly denseD ≠ 0 := by
      simpa only [denseD, CPolyEngine.toPoly_convert] using hd
    have hnormalDense :
        @IsNormalSqfree _ _ ⟨Differential.implicitDeriv (CPoly.toPoly denseDt)⟩
          (CPoly.toPoly denseD) := by
      rw [hDt]
      simpa only [denseD, CPolyEngine.toPoly_convert] using hnormal
    have hproperDense : (CPoly.toPoly denseA).degree < (CPoly.toPoly denseD).degree := by
      simpa only [denseA, denseD, CPolyEngine.toPoly_convert] using hproper
    have hdegreeDense : (CPoly.toPoly denseDt).natDegree ≤ 1 := by
      simpa only [denseDt, CPolyEngine.toPoly_convert] using hdegree
    have h := instLawfulCHermiteReductionDenseWf.remainder_proper
      denseDt denseA denseD hdense hnormalDense hproperDense hdegreeDense
    simpa only [hermiteResult_sparse_eq, sparseHermiteCompute, denseDt, denseA, denseD,
      CPolyEngine.toPoly_convert] using h

end DeepWiki.SymbolicIntegration
