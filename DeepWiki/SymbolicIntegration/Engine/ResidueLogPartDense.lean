import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Engine.ResidueLogPart

/-! # Checked dense residue-logarithm realization

The dense Rothstein-Trager computation exposes logarithmic terms only after denominator and identity checks. -/

namespace DeepWiki.SymbolicIntegration

open CFrac Polynomial

universe u v

namespace DensePoly

variable {α : Type u} [CField α] [CDiffField α] [CPolyGcd DensePoly α]
  [CPolyResultant DensePoly] [CResidueSource DensePoly α]

/-- Checked dense residue-logarithm extraction using the selected residue candidate source. -/
def checkedResidueLogPart (Dt hNum Dstar : DensePoly α) : Option (List (α × DensePoly α)) :=
  let resultant := cResidueResultantTower Dt hNum Dstar
  let candidates := CResidueSource.candidates resultant
  let logs := cLogPart Dt hNum Dstar candidates
  let result : IntegralResult α := ⟨(CPoly.czero, CPoly.one), logs⟩
  if (!cisZero Dstar && logs.all (fun cv => !cisZero cv.2)) &&
      CPoly.checkIdentity Dt result hNum Dstar then some logs else none

end DensePoly

/-- Dense realization of the option-valued residue-logarithm operation. -/
instance instCResidueLogPartDense {α : Type u} [CField α] [CDiffField α]
    [CPolyGcd DensePoly α] [CPolyResultant DensePoly]
    [CResidueSource DensePoly α] : CResidueLogPart DensePoly α where
  compute := DensePoly.checkedResidueLogPart

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α]
  [CDiffFieldSpec.{u,v} α] [Algebra ℚ (CFieldSpec.K α)]
  [CPolyGcd DensePoly α] [CPolyResultant DensePoly] [CResidueSource DensePoly α]

/-- The checked dense residue-logarithm operation is sound. -/
instance instLawfulCResidueLogPartDense : LawfulCResidueLogPart (P := DensePoly) (α := α) where
  sound Dt hNum Dstar logs hrun := by
    change DensePoly.checkedResidueLogPart Dt hNum Dstar = some logs at hrun
    simp only [DensePoly.checkedResidueLogPart] at hrun
    let raw := DensePoly.cLogPart Dt hNum Dstar
      (CResidueSource.candidates (DensePoly.cResidueResultantTower Dt hNum Dstar))
    let result : IntegralResult α := ⟨(CPoly.czero, CPoly.one), raw⟩
    by_cases hguard : ((!DensePoly.cisZero Dstar && raw.all (fun cv => !DensePoly.cisZero cv.2)) &&
        CPoly.checkIdentity Dt result hNum Dstar) = true
    · rw [if_pos hguard] at hrun
      have hlogsEq : raw = logs := Option.some.inj hrun
      subst logs
      rw [Bool.and_eq_true] at hguard
      obtain ⟨hpre, hcheck⟩ := hguard
      rw [Bool.and_eq_true] at hpre
      obtain ⟨hdenBool, hargsBool⟩ := hpre
      have hdenFalse : DensePoly.cisZero Dstar = false := by
        cases h : DensePoly.cisZero Dstar <;> simp [h] at hdenBool ⊢
      have hden : CPoly.toPoly Dstar ≠ 0 := by
        intro hz
        have hzBool : DensePoly.cisZero Dstar = true :=
          (LawfulCPolyEngine.cisZero_iff (P := DensePoly) Dstar).mpr hz
        rw [hzBool] at hdenFalse
        contradiction
      have hargs : ∀ cv ∈ raw, CPoly.toPoly cv.2 ≠ 0 := by
        intro cv hcv hz
        have hcvBool := (List.all_eq_true.mp hargsBool) cv hcv
        have hzBool : DensePoly.cisZero cv.2 = true :=
          (LawfulCPolyEngine.cisZero_iff (P := DensePoly) cv.2).mpr hz
        rw [hzBool] at hcvBool
        contradiction
      have hone : CPoly.toPoly (CPoly.one : DensePoly α) ≠ 0 := by
        rw [CPoly.toPoly_one]
        exact one_ne_zero
      have hid := field_identity_of_checkIdentityP Dt result hNum Dstar hone hden hargs hcheck
      refine ⟨?_⟩
      simpa only [result, logResidueSumP, towerFractionFieldDerivP_logDeriv,
        CPoly.toPoly_czero, CPoly.toPoly_one, map_zero, map_one, zero_div, zero_add] using hid
    · rw [if_neg hguard] at hrun
      contradiction

end DeepWiki.SymbolicIntegration
