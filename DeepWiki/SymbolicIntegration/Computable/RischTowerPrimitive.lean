import DeepWiki.SymbolicIntegration.Computable.IntegratorCases
import DeepWiki.SymbolicIntegration.Computable.CanonicalReconstructionCharZero
import DeepWiki.SymbolicIntegration.Computable.PrimitiveGuarded

/-! # Primitive-case special-part soundness (shared by the primitive solvers)

`primitiveGuardedCase_specialSound`: the special (polynomial/RDE) part of the primitive monomial case
integrates soundly. Under the `primitiveGuardedCase` guard (`b = 0`, `Dθ = 1`, constant `fₚ`) the polynomial
RDE is solved and `canonicalReconstruction_of_charZero` closes the reconstruction with the special term
vanishing; off the guard the hook returns `none`. This `K`-level identity is the `specialSound` field of the
LRT primitive base `instLawfulRischLevelLrtPrimitive` (`RischTowerLrt.lean`) — independent of any reduced
frontier, so the recursive solver reuses it. See `docs/recursive-lrt-typeclass.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial Classical
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CRischField α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

/-- **Primitive special-part soundness** (shared by the rational and LRT primitive solvers). The special
part is `primitiveGuardedCase.integrateSpecial`: under the guard (`b = 0`, `Dθ = 1`, constant `fₚ`) it solves
the polynomial RDE and the reconstruction (`canonicalReconstruction_of_charZero`) closes with the special term
vanishing; off the guard the hook returns `none`. Independent of any reduced frontier, so both solvers reuse
it. -/
theorem primitiveGuardedCase_specialSound [Fact (GcdFFCorrect (α := α))]
    (Dt a d snum sden : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (hhook : primitiveGuardedCase.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d)
      (crSpecDen Dt a d) = some (snum, sden)) :
    toPolyG sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K α),
      towerFractionFieldDerivG Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d := by
  simp only [primitiveGuardedCase] at hhook
  by_cases hguard : (cisZeroG (crSpecNum Dt a d) && cisZeroG (csubG Dt [CField.one])
      && cisZeroG (cmapDeriv (crPoly Dt a d))) = true
  · rw [if_pos hguard] at hhook
    rw [Bool.and_eq_true, Bool.and_eq_true] at hguard
    obtain ⟨⟨hb, hDt1g⟩, hconstg⟩ := hguard
    rcases hqp : cPolyRischDEGWf Dt [] (crPoly Dt a d) ((cdegG (crPoly Dt a d) : ℤ) + 1) with _ | qp
    · rw [hqp] at hhook; simp at hhook
    · rw [hqp] at hhook
      simp only [Option.some.injEq, Prod.mk.injEq] at hhook
      obtain ⟨rfl, rfl⟩ := hhook
      have hDt1 : toPolyG Dt = 1 := by
        have hh := (cisZeroG_iff (csubG Dt [CField.one])).mp hDt1g
        simpa only [denote, toPolyG_one_singleton, sub_eq_zero] using hh
      have hconst := mapCoeffs_eq_zero_of_cisZeroG_cmapDeriv (crPoly Dt a d) hconstg
      refine ⟨?_, fieldFrac (crPoly Dt a d) [CField.one], ?_, ?_⟩
      · rw [toPolyG_one_singleton]; exact one_ne_zero
      · exact primitive_special_identity Dt (crPoly Dt a d) qp hDt1 hconst hqp
      · have hvan : fieldFrac (crSpecNum Dt a d) (crSpecDen Dt a d) = 0 := by
          simp only [fieldFrac, (cisZeroG_iff (crSpecNum Dt a d)).mp hb, map_zero, zero_div]
        have hrec := canonicalReconstruction_of_charZero (Fact.out (p := GcdFFCorrect (α := α))) Dt a d hd0
        rw [hvan, add_zero] at hrec
        exact hrec
  · rw [if_neg hguard] at hhook; simp at hhook

end DeepWiki.SymbolicIntegration
