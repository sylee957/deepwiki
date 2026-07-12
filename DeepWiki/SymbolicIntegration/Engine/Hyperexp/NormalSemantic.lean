import DeepWiki.SymbolicIntegration.Engine.Hyperexp.NormalCore
import DeepWiki.SymbolicIntegration.Engine.RischFieldSpec
import DeepWiki.SymbolicIntegration.Engine.Assemble

/-! # Semantic hyperexponential residual correction

The residual-feedback normal stage is complete once its uncorrected normal result has the expected
residual identity and the scalar residual RDE is solvable in the coefficient field.
-/

namespace DeepWiki.SymbolicIntegration

open CFrac Polynomial

universe u

variable {α : Type u} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CRischField α] [Algebra ℚ (CFieldSpec.K α)]

/-- A raw hyperexponential normal result whose logarithmic residual is exactly
`cHyperexpResidual η logs`. -/
def IsHyperexpResidualNormalResult (Dt : DensePoly α) (η : α) (a d : DensePoly α)
    (red : IntegralResult α) : Prop :=
  CPoly.toPoly red.rational.2 ≠ 0 ∧
    (∀ cv ∈ red.logs, CFieldSpec.toK (CDiffField.cderiv cv.1) = 0) ∧
    (∀ cv ∈ red.logs, CPoly.toPoly cv.2 ≠ 0) ∧
    towerFractionFieldDerivP Dt (fieldFracP red.rational.1 red.rational.2) +
      logResidueSumP Dt red.logs = fieldFracP a d +
        fieldFracP [DensePoly.cHyperexpResidual η red.logs] [CCommRing.one]

/-- Semantic domain of scalar residual correction: the raw residual identity and a solution of
`Dq = cHyperexpResidual η logs`. -/
def HyperexpResidualCorrectionDomain (Dt : DensePoly α) (η : α) (a d : DensePoly α)
    (red : IntegralResult α) : Prop :=
  IsHyperexpResidualNormalResult Dt η a d red ∧
    CFieldRDESolvable (CCommRing.zero : α) (DensePoly.cHyperexpResidual η red.logs)

/-- Field-RDE completeness executes residual correction and yields a certified normal result. -/
theorem cCorrectHyperexpNormal_exists_of_domain [CRischFieldSpec α]
    (hcomplete : CRischFieldComplete α) (Dt : DensePoly α) (η : α) (a d : DensePoly α)
    (red : IntegralResult α)
    (hdomain : HyperexpResidualCorrectionDomain Dt η a d red) :
    ∃ out, DensePoly.cCorrectHyperexpNormal η red = some out ∧ CertifiedNormalResult Dt a d out := by
  obtain ⟨hred, hsolvable⟩ := hdomain
  obtain ⟨hden, hconstants, hargs, hidentity⟩ := hred
  let residual := DensePoly.cHyperexpResidual η red.logs
  obtain ⟨intR, hsolve⟩ := crischDESolve_exists_of_complete hcomplete
    (CCommRing.zero : α) residual hsolvable
  let newNum := CPolyEngine.sub red.rational.1
    (CPolyEngine.mul (CPolyEngine.ofCoeffList [intR]) red.rational.2)
  let out : IntegralResult α := ⟨(newNum, red.rational.2), red.logs⟩
  have hrun : DensePoly.cCorrectHyperexpNormal η red = some out := by
    simp only [DensePoly.cCorrectHyperexpNormal, residual, hsolve, newNum, out]
  refine ⟨out, hrun, ?_⟩
  refine ⟨?_, hden, hconstants, hargs⟩
  have hintDeriv : towerFractionFieldDerivP Dt
      (fieldFracP ([intR] : DensePoly α) [CCommRing.one]) =
      fieldFracP ([residual] : DensePoly α) [CCommRing.one] := by
    simpa only [towerFractionFieldDerivP, towerFractionFieldDeriv, fieldFracP,
      toPoly_list_eq, denote, mul_zero, add_zero, map_one, div_one] using
      crischDESolve_zero_intDeriv Dt residual intR hsolve
  have hfrac : fieldFracP newNum red.rational.2 =
      fieldFracP red.rational.1 red.rational.2 -
        fieldFracP ([intR] : DensePoly α) [CCommRing.one] := by
    have hnew : CPoly.toPoly newNum = CPoly.toPoly red.rational.1 -
        CPoly.toPoly ([intR] : DensePoly α) * CPoly.toPoly red.rational.2 := by
      dsimp only [newNum]
      rw [CPolyEngine.toPoly_sub, LawfulCPolyEngine.toPoly_mul,
        CPolyEngine.ofCoeffList_dense_eq]
    have hsingleton : CPoly.toPoly ([intR] : DensePoly α) = Polynomial.C (CFieldSpec.toK intR) := by
      rw [toPoly_list_eq]
      simp only [denote, mul_zero, add_zero]
    have hone : CPoly.toPoly ([CCommRing.one] : DensePoly α) = 1 := by
      rw [toPoly_list_eq]
      simp only [denote, mul_zero, add_zero, map_one]
    simp only [fieldFracP, hnew, hsingleton, hone, map_sub, map_mul, map_one, div_one]
    have hAden : am α (CPoly.toPoly red.rational.2) ≠ 0 := am_ne_zero hden
    field_simp
  change towerFractionFieldDerivP Dt (fieldFracP newNum red.rational.2) +
      logResidueSumP Dt red.logs = fieldFracP a d
  rw [hfrac, map_sub]
  have hidentity' : towerFractionFieldDerivP Dt (fieldFracP red.rational.1 red.rational.2) +
      logResidueSumP Dt red.logs = fieldFracP a d +
        fieldFracP ([residual] : DensePoly α) [CCommRing.one] := by
    simpa only [residual] using hidentity
  calc
        towerFractionFieldDerivP Dt (fieldFracP red.rational.1 red.rational.2) -
        towerFractionFieldDerivP Dt (fieldFracP ([intR] : DensePoly α) [CCommRing.one]) +
        logResidueSumP Dt red.logs =
        (towerFractionFieldDerivP Dt (fieldFracP red.rational.1 red.rational.2) +
          logResidueSumP Dt red.logs) -
          towerFractionFieldDerivP Dt (fieldFracP ([intR] : DensePoly α) [CCommRing.one]) := by ring
    _ = (fieldFracP a d + fieldFracP ([residual] : DensePoly α) [CCommRing.one]) -
          fieldFracP ([residual] : DensePoly α) [CCommRing.one] := by rw [hidentity', hintDeriv]
    _ = fieldFracP a d := by ring

end DeepWiki.SymbolicIntegration
