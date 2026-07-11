import DeepWiki.ComputableAlgebra.PolyReprConvert
import DeepWiki.SymbolicIntegration.Engine.CanonicalReconstructionCharZero

/-! # Sparse canonical-representation realization

The sparse-facing stage transports the lawful dense splitter through denotation-preserving conversion. -/

namespace DeepWiki.SymbolicIntegration

open CFrac Polynomial

universe u v

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
  [CRischField α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
  [CPolyGcd DensePoly α] [LawfulCPolyGcd.{u,v} DensePoly α]
  [CPolySplitFactor DensePoly α] [LawfulCPolySplitFactor DensePoly α]

private def sparseCanonicalCompute (Dt a d : CPoly.SparsePoly α) :
    CanonicalRepresentationResult CPoly.SparsePoly α :=
  let denseDt : DensePoly α := CPolyEngine.convert Dt
  let denseA : DensePoly α := CPolyEngine.convert a
  let denseD : DensePoly α := CPolyEngine.convert d
  let out := canonicalResult denseDt denseA denseD
  { polynomial := CPolyEngine.convert out.polynomial
    specialNum := CPolyEngine.convert out.specialNum
    specialDen := CPolyEngine.convert out.specialDen
    normalNum := CPolyEngine.convert out.normalNum
    normalDen := CPolyEngine.convert out.normalDen }

/-- Sparse realization of canonical representation through a denotation-preserving dense backend. -/
instance instCCanonicalRepresentationSparse : CCanonicalRepresentation CPoly.SparsePoly α where
  compute := sparseCanonicalCompute

omit [CFieldSpec α] [CDiffFieldSpec α] [CRischField α] [Algebra ℚ (CFieldSpec.K α)]
  [CharZero (CFieldSpec.K α)] [CPolyGcd DensePoly α] [LawfulCPolyGcd DensePoly α]
  [LawfulCPolySplitFactor DensePoly α] in
private theorem canonicalResult_sparse_eq (Dt a d : CPoly.SparsePoly α) :
    canonicalResult Dt a d = sparseCanonicalCompute Dt a d := rfl

/-- The sparse canonical realization satisfies the representation-neutral stage contract. -/
instance instLawfulCCanonicalRepresentationSparse :
    LawfulCCanonicalRepresentation (P := CPoly.SparsePoly) (α := α) where
  reconstruction Dt a d hd := by
    let denseDt : DensePoly α := CPolyEngine.convert Dt
    let denseA : DensePoly α := CPolyEngine.convert a
    let denseD : DensePoly α := CPolyEngine.convert d
    have hdense : CPoly.toPoly denseD ≠ 0 := by
      simpa only [denseD, CPolyEngine.toPoly_convert] using hd
    have h := LawfulCCanonicalRepresentation.reconstruction (P := DensePoly) denseDt denseA denseD hdense
    let out := canonicalResult denseDt denseA denseD
    change fieldFracP (CPolyEngine.convert out.polynomial) CPoly.one
          + fieldFracP (CPolyEngine.convert out.specialNum) (CPolyEngine.convert out.specialDen)
          + fieldFracP (CPolyEngine.convert out.normalNum) (CPolyEngine.convert out.normalDen)
        = fieldFracP a d
    calc
      _ = fieldFracP out.polynomial CPoly.one
            + fieldFracP out.specialNum out.specialDen
            + fieldFracP out.normalNum out.normalDen := by
          simp only [fieldFracP, CPolyEngine.toPoly_convert, CPoly.toPoly_one]
      _ = fieldFracP denseA denseD := h
      _ = fieldFracP a d := by
          simp only [fieldFracP, denseA, denseD, CPolyEngine.toPoly_convert]
  specialDen_nonzero Dt a d hd := by
    let denseDt : DensePoly α := CPolyEngine.convert Dt
    let denseA : DensePoly α := CPolyEngine.convert a
    let denseD : DensePoly α := CPolyEngine.convert d
    have hdense : CPoly.toPoly denseD ≠ 0 := by
      simpa only [denseD, CPolyEngine.toPoly_convert] using hd
    have h := LawfulCCanonicalRepresentation.specialDen_nonzero (P := DensePoly)
      denseDt denseA denseD hdense
    simpa only [canonicalResult_sparse_eq, sparseCanonicalCompute, denseDt, denseA, denseD,
      CPolyEngine.toPoly_convert] using h
  normalDen_nonzero Dt a d hd := by
    let denseDt : DensePoly α := CPolyEngine.convert Dt
    let denseA : DensePoly α := CPolyEngine.convert a
    let denseD : DensePoly α := CPolyEngine.convert d
    have hdense : CPoly.toPoly denseD ≠ 0 := by
      simpa only [denseD, CPolyEngine.toPoly_convert] using hd
    have h := LawfulCCanonicalRepresentation.normalDen_nonzero (P := DensePoly)
      denseDt denseA denseD hdense
    simpa only [canonicalResult_sparse_eq, sparseCanonicalCompute, denseDt, denseA, denseD,
      CPolyEngine.toPoly_convert] using h
  normal_proper Dt a d hd := by
    let denseDt : DensePoly α := CPolyEngine.convert Dt
    let denseA : DensePoly α := CPolyEngine.convert a
    let denseD : DensePoly α := CPolyEngine.convert d
    have hdense : CPoly.toPoly denseD ≠ 0 := by
      simpa only [denseD, CPolyEngine.toPoly_convert] using hd
    have h := LawfulCCanonicalRepresentation.normal_proper (P := DensePoly)
      denseDt denseA denseD hdense
    simpa only [canonicalResult_sparse_eq, sparseCanonicalCompute, denseDt, denseA, denseD,
      CPolyEngine.toPoly_convert] using h
  normal_isNormalSqfree Dt a d hd := by
    let denseDt : DensePoly α := CPolyEngine.convert Dt
    let denseA : DensePoly α := CPolyEngine.convert a
    let denseD : DensePoly α := CPolyEngine.convert d
    have hdense : CPoly.toPoly denseD ≠ 0 := by
      simpa only [denseD, CPolyEngine.toPoly_convert] using hd
    have h := LawfulCCanonicalRepresentation.normal_isNormalSqfree (P := DensePoly)
      denseDt denseA denseD hdense
    have hDt : CPoly.toPoly denseDt = CPoly.toPoly Dt := by
      exact CPolyEngine.toPoly_convert Dt
    change @IsNormalSqfree _ _
      ⟨Differential.implicitDeriv (CPoly.toPoly denseDt)⟩
      (CPoly.toPoly (canonicalResult denseDt denseA denseD).normalDen) at h
    rw [hDt] at h
    change @IsNormalSqfree _ _
      ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
      (CPoly.toPoly (canonicalResult Dt a d).normalDen)
    simpa only [canonicalResult_sparse_eq, sparseCanonicalCompute, canonicalResult, denseDt, denseA,
      denseD, CPolyEngine.toPoly_convert] using h

end DeepWiki.SymbolicIntegration
